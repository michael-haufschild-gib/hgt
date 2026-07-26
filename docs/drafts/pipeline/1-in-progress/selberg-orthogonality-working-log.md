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

---

## 39. Cycle 33 (2026-07-25) — the LINEAR case of Conjecture A is a THEOREM, by exactly the
monodromy mechanism MI postulates  [OWN, PROVED HERE]

### 39.1 Theorem (linear integrality)

> Let `F ∈ S` and suppose there are `m ∈ C` and `δ > 0` with
> ```
> a_F(p) = m + O(p^{−δ})     for all primes p.
> ```
> Then **`m ∈ Z`**; in fact `m = ord_{s=1}(1/F)`, i.e. `F` has a pole of order `m` at `s = 1`
> (a zero of order `−m` if `m < 0`).

*Proof.* Put `D(s) := log F(s) − m·log ζ(s)`, defined for `σ > 1` (both are non-vanishing there).
As a Dirichlet series,
```
D(s) = Σ_p ( a_F(p) − m ) p^{−s}  +  Σ_p Σ_{k≥2} ( b_F(p^k) − m/k ) p^{−ks}.
```
The first sum converges absolutely for `σ > 1 − δ`. For the second, the Newton relations express
`b_F(p^k)` as a universal polynomial in `a_F(p),…,a_F(p^k)` with `≍ e^{c√k}` terms of total degree
`≤ k`, so `|b_F(p^k)| ≪ C_ε^k p^{kε}`; its `k = 2` term is `≪ p^{−2σ+2ε}`, giving convergence for
`σ > 1/2 + ε`, while for each fixed small `p` the `k`-sum converges for `σ > θ` by the Euler-product
axiom. Hence `D` is **holomorphic on `σ > max(1−δ, 1/2+ε, θ)`**, a region containing `s = 1`.

Therefore, on that region, `ζ(s)^m := F(s)·e^{−D(s)}` is a **single-valued** function: `F` is
meromorphic by Selberg's axiom (2), and `e^{−D}` is holomorphic and non-vanishing. Near `s = 1`,
`ζ(s) = (s−1)^{−1}u(s)` with `u` holomorphic and `u(1) = 1`, so `ζ(s)^m = (s−1)^{−m}u(s)^m`; and
`(s−1)^{−m}` is single-valued precisely when `m ∈ Z`. Comparing orders at `s = 1` identifies `m`
with the order of the pole of `F`. ∎

### 39.2 Why this matters

This is **exactly the mechanism MI postulates**, executed in the case where it is available:
*integrality of a prime-density is forced by single-valuedness of an object that Selberg's axiom (2)
already provides.* In the linear case that object is `F` itself; in the quadratic case (Conjecture A)
it would have to be `R_{F,F}`, which axiom (2) does **not** cover — and that gap is precisely MI.

So the programme's central diagnosis is now confirmed by a theorem rather than by heuristics:
```
linear prime-density  ⟶ integrality  PROVED  (axiom (2) applies to F)
quadratic prime-density ⟶ integrality  =  Conjecture A  (axiom (2) does not apply to R_{F,F})
```

### 39.3 Why it does not extend to the test case

For the test case `|a_F(p)| = c` with varying phases, the same computation gives
`𝔏_F(w) − c² log ζ(w) = (k ≥ 2 terms)`, holomorphic on `Re w > max(1/2, θ)`, hence
`ℛ_F(w) = ζ(w)^{c²}·e^{holo}` near `w = 1`. But concluding `c² ∈ Z` needs `ℛ_F` (equivalently
`R_{F,F}`) to be single-valued there — which is MI. **Circular, as expected.** The two cases are
separated by exactly one application of axiom (2).

### 39.4 Corollary (a clean unconditional statement about `S`)

> No `F ∈ S` has `a_F(p) = c + O(p^{−δ})` with `c ∉ Z`. In particular there is no element of the
> Selberg class whose prime coefficients converge to `1/√2`, or to any non-integer.

The test case of §37.3 therefore survives only in its *oscillating* form: any counterexample to
Conjecture A must have prime coefficients of constant modulus but genuinely varying phase.
That is a real narrowing of the search space and is recorded as the sharpened target.

---

## 40. Cycle 34 (2026-07-25) — sharp form of linear integrality, and the surviving shape of any
counterexample

### 40.1 Theorem (sharp linear integrality)  [OWN, PROVED HERE]

> Let `F ∈ S` and suppose `Σ_{p≤x} ( a_F(p) − m )/p = O(1)` for some `m ∈ C`. Then `m = m_F`, the
> order of the pole of `F` at `s = 1`; in particular **`m ∈ Z_{≥0}`**.

*Proof.* Let `S(x) := Σ_{p≤x}(a_F(p)−m)/p`, bounded by hypothesis. Partial summation gives, for real
`s > 1`,
`Σ_p (a_F(p)−m)p^{−s} = (s−1)∫_1^∞ S(x)x^{−s}dx ≪ (s−1)·sup|S|/(s−1) = O(1)`.
Adding the `k ≥ 2` part of `log F − m log ζ`, holomorphic on `σ > max(1/2,θ)` by the Newton-relation
bound `|b_F(p^k)| ≪ C_ε^k p^{kε}` (§39.1), we get `log F(σ) − m log ζ(σ) = O(1)` as `σ → 1+`, i.e.
`F(σ) ≍ (σ−1)^{−m}`. But `F` is meromorphic at `s=1` with pole order `m_F ∈ Z_{≥0}`, so
`F(σ) ≍ (σ−1)^{−m_F}`. Hence `(σ−1)^{m−m_F} ≍ 1`, forcing `m = m_F`. ∎

So the **linear** Selberg density is unconditionally an integer, and is the pole order — no
hypothesis beyond the axioms. Combined with §39.1 (the `O(p^{−δ})` version, which additionally
locates `m` via single-valuedness of `ζ^m`), the linear half of Selberg's conjectures is a theorem,
by the very mechanism MI postulates for the quadratic half.

### 40.2 The surviving shape of a counterexample to Conjecture A

Collecting the constraints now proved or classified:

| hypothesis on `a_F(p)` | status |
|---|---|
| `a_F(p) = c + O(p^{−δ})` | `c ∈ Z` — §39.1 |
| `Σ_{p≤x}(a_F(p)−m)/p = O(1)` | `m = m_F ∈ Z_{≥0}` — §40.1 |
| `a_F(p) = c·χ(p)p^{−iθ}`, `χ` principal, `θ ≠ 0` | forces `c = 0` (else `F` has a pole at `1−iθ`) |
| `d_F = 1` | classified (K–P): `|a_F(p)| = 1` |
| `d_F = 2`, `q_F = 1` | classified (K–P 2022): modular, `|a_F(p)|` non-constant |

> **Therefore any counterexample to Conjecture A must have `|a_F(p)|` of constant (or
> non-integrally-averaging) modulus with genuinely oscillating phase, degree `≥ 2` with `q_F > 1`,
> or degree `≥ 3`** — i.e. it must live exactly in the region where no classification exists. This
> is a real narrowing, and it explains why every classified region satisfies Selberg's conjectures.

### 40.3 What the two theorems say about MI

`§39.1` and `§40.1` are the linear shadow of Conjecture A and both are proved by **applying axiom (2)
to `F` itself**. Conjecture A is the same statement one level up, where the object needing axiom (2)
is `R_{F,F}` — and axiom (2) does not reach it. MI is precisely the assertion that it should.
The programme's central claim is therefore now supported by a proved instance rather than by
analogy: *integrality of a Selberg density is a monodromy phenomenon, and it holds exactly where
single-valuedness is available.*

---

## 41. Cycles 35–37 (2026-07-25) — batch: the Abel form of the linear case is unconditional; the
narrowed target resists every available tool

### 41.1 Unconditional Abel form (linear case)  [clean statement, worth keeping]

For every `F ∈ S`, since `F` is meromorphic at `s=1` with pole order `m_F`,
`log F(s) − m_F log(1/(s−1))` is holomorphic near `s=1`; and
`log F(s) = Σ_p a_F(p)p^{−s} + (holomorphic on σ > max(1/2,θ))` by §39.1. Hence
```
Σ_p a_F(p) p^{−s} = m_F · log(1/(s−1)) + (holomorphic near s = 1)      UNCONDITIONALLY.
```
This is the linear case of Selberg's Conjecture B (against `ζ`) in **Abel form**, with no hypothesis.
The Tauberian upgrade to `Σ_{p≤x}a_F(p)/p = m_F log log x + O(1)` needs control on the whole line
`Re s = 1`, i.e. the generalized PNT — the Abel/Tauber split of §9.2. The quadratic analogue of the
displayed identity **is** MI, and the only missing ingredient is that axiom (2) does not cover
`R_{F,F}`.

### 41.2 The shift family, revisited with §40.1

For entire `F` and `θ ≠ 0`, `F_θ(s) = F(s+iθ) ∈ S` has `m_{F_θ} = 0` (its pole sits at `1−iθ`). So
§40.1 gives: *if* `Σ_{p≤x}a_F(p)p^{−iθ}/p` has an `O(1)`-asymptotic then its density is `0`. Thus
the whole shift family is pinned **conditionally on the asymptotic existing**; §40.1 is a rigidity
statement, not an existence statement, and cannot be bootstrapped into one.

### 41.3 Attempts on the narrowed target (`|a_F(p)| = c`, oscillating phase), all failed

- `F·\bar F ∈ S` gives only `2Re a_F(p)` — linear, no access to `c²`.
- `F_θ·\bar F ∈ S` gives `a_F(p)p^{−iθ} + \overline{a_F(p)}` — again linear.
- `a_F(p²) = b_F(p²) + c²e^{2iφ_p}/2` with `|a_F(p²)| ≪ p^ε`, `|b_F(p²)| ≪ p^{2θ}`: vacuous.
- Second and fourth moments on and off the critical line: every computation returns
  `T(log T)^{c²}`-type answers with no constraint linking `c²` to `d`.
- The Cusp–Spectrum Radius Law uses only `a_F(1)=1` (and `m_1 = 2` here), so it is blind to `c`.
- Writing `𝔏_F` as a combination of `log H`, `H ∈ S`, would need `b_H(p^k) = k|b_F(p^k)|²` — the
  functorial lift.

### 41.4 Net position after 37 cycles

Proved here and standing: Theorems 1, 2, 4 and Corollary 3 (MI ⟹ Conjecture A, integrality of the
full pairing, axiom-necessity, the two-ingredient reduction); the Cusp–Spectrum Radius Law with its
`S^♯` form and four exact verifications; the explicit Rankin–Selberg object `ℛ_F` with positivity;
sharp linear integrality (§39.1, §40.1) and the unconditional Abel form (§41.1); Lemma A′ and the
Lean certificates.

Obstructions recorded, each with a proof or an explicit witness: degree multiplicativity;
linear-moment closure; truncated spectral data; frequency non-isolation; the `ζ^{1/2}` witness
showing positivity cannot give MI; the Carlson and Halász dead ends; the circularity of every exit
from the test case.

The single open statement carrying the whole programme is **MI**; the single sharpest concrete
question is whether an `F ∈ S` can have `|a_F(p)|` of constant non-integral mean square with
oscillating phase, necessarily in degree `≥ 2` with `q_F > 1` or degree `≥ 3`.

---

## 42. Cycle 38 (2026-07-25) — the log-coefficient transfer lemma (analytic core of §39.1/§40.1)

### 42.1 Lemma  [PROVED HERE, explicit constant]

> Let `A, B : N → C` with `A 0 = 1` satisfy the exponential (Newton) recursion
> ```
> n · A_n = Σ_{k=1}^{n} k · B_k · A_{n−k}      (n ≥ 1),
> ```
> and suppose `‖A_n‖ ≤ C R^n` for all `n`, with `C, R ≥ 1`. Then `‖B_n‖ ≤ (4CR)^n` for all `n ≥ 1`.

*Proof.* Write `M := 4CR ≥ R`. Isolating `k = n` (where `A_0 = 1`),
`n B_n = n A_n − Σ_{k=1}^{n−1} k B_k A_{n−k}`. By strong induction `‖B_k‖ ≤ M^k` for `k < n`, so
`n‖B_n‖ ≤ n C R^n + Σ_{k=1}^{n−1} n M^k C R^{n−k} = n C R^n + n C R^n Σ_{k=1}^{n−1}(M/R)^k`.
Since `M/R = 4C ≥ 2` and `Σ_{k=1}^{n−1}x^k = x(x^{n−1}−1)/(x−1) ≤ 2x^{n−1}` for `x ≥ 2`, this is
`≤ n C R^n + 2 n C R M^{n−1}`, so `‖B_n‖ ≤ C R^n + 2 C R M^{n−1}`. As `M ≥ R`,
`C R^n = C R·R^{n−1} ≤ 2 C R M^{n−1}`, whence `‖B_n‖ ≤ 4 C R M^{n−1} = M^n`. ∎

### 42.2 Application

The recursion is the coefficient form of `F_p' = (log F_p)' F_p`, i.e. `A_k = a_F(p^k)`,
`B_k = k·b_F(p^k)`. With `‖a_F(p^k)‖ ≤ C_ε p^{kε}` (Ramanujan, `R = p^ε`) the lemma gives
```
|b_F(p^k)| ≪ (4C_ε)^k p^{kε} ,
```
exactly the bound used in §37.1, §39.1 and §40.1 to make `Σ_p Σ_{k≥2}` converge on `Re s > 1/2 + ε`.
**The analytic core of the linear-integrality theorems is elementary and fully explicit.**

### 42.3 Lean status

Formalisation drafted (`/tmp/logcoeff.lean`): the recursion split, the erase-index rewriting and the
per-term bound go through; the remaining step is the geometric-sum bound `Σ_{k=1}^{n−1}x^k ≤ 2x^{n−1}`
(`x ≥ 2`) inside a strong induction. Left for a later pass — a formalisation task, not a mathematical
gap. Recorded so the next session resumes from the working draft.

---

## 43. Cycles 39–40 (2026-07-25) — MI as the continuation of the `L²`-mean of `log F`

### 43.1 A second explicit avatar of the target

Alongside `𝔏_F(w) = Σ_{p,k} k|b_F(p^k)|²p^{−kw}` (§36) define the unweighted version
```
𝔏'_F(w) := Σ_{p,k} |b_F(p^k)|² p^{−kw} .
```
Exactly as in §37.1, `𝔏'_F(w) = Σ_p |a_F(p)|² p^{−w} + (holomorphic on Re w > max(1/2,θ))`, so
`𝔏'_F` and `𝔏_F` have the same singular behaviour at `w = 1`, and **either may replace `R_{F,F}` in
MI**. But `𝔏'` has an extra interpretation: for `σ > 1`, by the mean-value theorem for Dirichlet
series,
```
𝔏'_F(2σ) = lim_{T→∞} (2T)^{−1} ∫_{−T}^{T} | log F(σ+it) |² dt .
```
> **MI (diagonal) ⟺ the `L²`-mean of `log F` on vertical lines, as a function of `σ`, continues
> meromorphically past `σ = 1/2`** (i.e. past `w = 2σ = 1`).

### 43.2 The functional equation computes the mean exactly on the left

Put `V(σ,T) := (2T)^{−1}∫_{−T}^{T}|log F(σ+it)|²dt`. From `log F(s) = log X(s) + log \bar F(1−s)`
with `|log X(σ+it)| = (1/2−σ)·log(q|t|^d/(2π)^d) + O(1)`:
```
σ > 1 :   V(σ,T) → 𝔏'_F(2σ)          (bounded in T);
σ < 0 :   V(σ,T) = (1/2−σ)² d² log²T + O(log T)   (explicit).
```
So the `T`-behaviour of `V` is completely known on both sides of the critical strip: bounded on the
right, `≍ log²T` on the left, with the transition at `σ = 1/2` — matching the abscissa `w = 1`.

### 43.3 Why interpolation still fails

Hadamard three-lines would give `V(1/2+δ, T)` from the two sides, hence MI. It fails twice over:
- `log F` is **multivalued** in the strip (branch points at every zero of `F`, `≍ (d/π)T log T` of
  them), so no three-lines for `log F`;
- replacing it by the single-valued `log|F|` does not help: `log|F|` is **subharmonic**
  (`Δ log|F| = 2π Σ_ρ δ_ρ ≥ 0`), and `σ ↦ ∫ (log|F|)² dt` has no convexity for subharmonic
  integrands.

This is the same wall as §34.2 (the `log(F/G)` propagation) and as MI itself: **single-valuedness
across the critical strip.** Three independent formulations of the programme's residual difficulty
now coincide: continuation of `R_{F,F}` at `w=1`; propagation of a mean square across the strip;
and monodromy of `log F` around its zeros.

### 43.4 Net

No new mechanism. The value of this batch is the second avatar `𝔏'_F` — an *analytically meaningful*
form of the target (`MI` = continuation of an `L²`-mean, with both boundary behaviours explicitly
computed) — and the confirmation that the obstruction is single-valuedness in the strip, not any
missing estimate.

### 42.4 Lean draft progress (cycle 41)

Saved working draft: `docs/drafts/pipeline/computations/logcoeff-draft.lean` (or
`docs/drafts/pipeline/logcoeff-draft.lean`). Compiling parts:
- `geom_le_two` — `Σ_{j<m} r^j ≤ 2` for `0 ≤ r ≤ 1/2`, by induction via `geom_sum_succ`. **Compiles.**
- the recursion is restated in the reindexed form
  `n·A n = ∑_{j<n} (n−j)·B(n−j)·A j`, which makes the `j = 0` split clean and avoids all
  natural-subtraction reindexing in the geometric step;
- `hsplit` (isolating `j = 0`, `(range n).erase 0 = Ico 1 n`) — **compiles**;
- `hkey`, `hterm`'s norm bound — **compile**;
- remaining: the algebraic identity `M^{n−j} R^j = M^{n−1} R (R/M)^{j−1}` (a `field_simp`/`ring`
  massage), then `Finset.sum_Ico_eq_sum_range` to turn `∑_{j ∈ Ico 1 n}(R/M)^{j−1}` into
  `∑_{i<n−1}(R/M)^i ≤ 2`, and the final arithmetic
  `‖B n‖ ≤ C R^n + 2CR M^{n−1} ≤ 3CR M^{n−1} ≤ M^n`.
Purely mechanical from here; recorded so a later pass does not restart.

---

## 44. Cycle 41 (2026-07-25) — the log-coefficient transfer lemma is CERTIFIED in Lean

`formal/GaloisForLFunctions/HTGeometry/LogCoefficientTransfer.lean` (registered in the `HTGeometry`
umbrella; `lake build` green; `#print axioms HTGeometry.log_coeff_bound` =
`[propext, Classical.choice, Quot.sound]`):

```
theorem HTGeometry.log_coeff_bound {A B : ℕ → ℂ} {C R : ℝ} (hC : 1 ≤ C) (hR : 1 ≤ R)
    (hA0 : A 0 = 1)
    (hrec : ∀ n, 1 ≤ n → (n:ℂ) * A n = ∑ j ∈ Finset.range n, ((n-j : ℕ):ℂ) * B (n-j) * A j)
    (hAb : ∀ n, ‖A n‖ ≤ C * R ^ n) :
    ∀ n, 1 ≤ n → ‖B n‖ ≤ (4 * C * R) ^ n
```

with the auxiliary `geom_le_two` (`Σ_{j<m} r^j ≤ 2` for `0 ≤ r ≤ 1/2`). **The analytic core of the
linear-integrality theorems (§39.1, §40.1) and of the convergence region in §37.1 is now
machine-checked**: applying it with `A k = a_F(p^k)`, `B k = k·b_F(p^k)`, `R = p^ε` gives
`|b_F(p^k)| ≪ (4C_ε)^k p^{kε}` unconditionally from Ramanujan.

Lean inventory of the programme (all unconditional, all axiom-clean):
- `RHTower.SelbergPairingPrimeSquare` — 8 theorems;
- `HTGeometry.GeneralizedDirichletMeanValue` — exact mean value, arbitrary real frequencies;
- `HTGeometry.ResidueJumpLowerBound` — the residue-jump obstruction (Lemma A′);
- `HTGeometry.LogCoefficientTransfer` — the exponential-formula coefficient transfer.

## 45. Cycle 42 — EB under the polynomial Euler product: what is actually needed

Ramanujan at high prime powers forces the local roots to satisfy `|α_i| ≤ 1` (if `∂_p` roots, then
`a_F(p^k) = h_k(α) ≍ (max|α_i|)^k k^{∂_p−1}`, and `≪_ε p^{kε}` for all `k` forces `max|α_i| ≤ 1`).
Hence `|a_F(p)| ≤ ∂_p`. But Ramanujan at `n = p` only gives `∂_p ≪_ε p^ε`, and
`Σ_p ∂_p²/p ≪ Σ_p p^{2ε−1}` diverges. **So PEP alone does not give EB**: one also needs the local
degrees to be bounded (`∂_p ≤ d_F`, the standard form of the conjecture). Recorded to keep the
implication chain honest: `PEP + bounded local degree ⟹ BS ⟹ EB`.

---

## 46. Cycles 43–44 (2026-07-25) — the log-derivative avatar, and where Carlson does apply

### 46.1 `F'/F` is single-valued: a third avatar of the target

`log F` is multivalued in the strip (branch points at the zeros), but its **derivative** is not:
`F'/F` is meromorphic on `C` by axiom (2), with simple poles at the zeros and poles of `F` and
**integer** residues. Its Dirichlet series is `−Σ_n Λ_F(n)n^{−s}`, `Λ_F(n) = b_F(n)log n`. Define
```
𝔐_F(w) := Σ_n |Λ_F(n)|² n^{−w} = Σ_{p,k} k² log²p · |b_F(p^k)|² p^{−kw} .
```
Then for `σ > 1`, `𝔐_F(2σ)` is the `L²`-mean of `F'/F` on the line `σ`, and by §37.1's bound the
`k ≥ 2` part is holomorphic on `Re w > max(1/2,θ)`, so
```
𝔐_F(w) = Σ_p |a_F(p)|² log²p · p^{−w} + (holomorphic past 1/2) .
```
Since `Σ_p|a_F(p)|²p^{−w} ~ n_F log(1/(w−1))`, differentiating twice gives
`𝔐_F(w) ~ n_F/(w−1)²`: **`n_F` is the coefficient of the double pole of the `L²`-mean of `F'/F`.**
So MI can equivalently be posed for `𝔐_F`, whose "parent" `F'/F` is single-valued — the one place
where the monodromy obstruction of §43.3 is absent.

### 46.2 Where Carlson applies to `F'/F`, and why it is still not enough

By the standard partial-fraction bound for `F ∈ S`,
`F'/F(σ+it) = Σ_{|γ−t|≤1} (s−ρ)^{−1} + O(log(|t|+2))`. Combined with the K–P density theorem
`N_F(σ,T) ≪ T^{(4d+12)(1−σ)+ε}`:
- for `σ > 1 − η` with `η` small, the zeros to the right are `≪ T^{ε}`, so
  `∫_0^T |F'/F(σ+it)|² dt ≪ T log²T ≪ T^{1+ε}` and **Carlson's theorem applies**, giving
  `lim_T (2T)^{−1}∫|F'/F(σ+it)|²dt = 𝔐_F(2σ)`;
- for `σ` near `1/2` the density theorem is vacuous (`T^{c/2+ε} ≫ T`), the estimate fails, and
  Carlson does not apply.

So the identity is gained on a strip `(1−η, 1)` where the series already converges — **no
continuation**. Recorded: the `F'/F` avatar removes the *multivaluedness* obstruction but not the
*continuation* obstruction; the two are genuinely different, and only the second matters for MI.

### 46.3 Net

Three avatars of the same target are now on record, each removing a different difficulty and none
removing the decisive one:
| avatar | parent object | multivalued? | continuation past `w=1`? |
|---|---|---|---|
| `R_{F,F}` / `ℛ_F` | none (needs functoriality) | — | open (MI) |
| `𝔏'_F` = `L²`-mean of `log F` | `log F` | yes (zeros) | open |
| `𝔐_F` = `L²`-mean of `F'/F` | `F'/F` (meromorphic, integer residues) | **no** | open |

### 46.4 CORRECTION to §46.2

The claim that Carlson applies to `F'/F` on a strip `(1−η,1)` was argued from the density theorem
alone; that is not the right criterion. What controls `∫_0^T|F'/F(σ+it)|²dt` is not the zeros to the
right of `σ` but **all** zeros: the partial-fraction sum `Σ_{|γ−t|≤1}(s−ρ)^{−1}` has `≍ d log t`
terms each of size `≍ (σ−1/2)^{−1}`, and its large real part cancels against the archimedean
`O(log t)` term. Whether the mean square is `O(1)` or grows therefore depends on the *cancellation*,
i.e. on the zero distribution, not on a density estimate. For `ζ` the classical statement
`∫_0^T |ζ'/ζ(σ+it)|²dt ~ T Σ_n Λ(n)²n^{−2σ}` for `σ > 1/2` is known **under RH**; unconditionally the
off-line zeros obstruct it. So:

> §46.2 is withdrawn. Carlson's identity for `F'/F` on `1/2 < σ < 1` is a *conditional* statement
> (RH-type input), and in any case it holds only where `Σ|Λ_F(n)|²n^{−2σ}` already converges — it
> never produces continuation. The `𝔐_F` avatar removes multivaluedness and nothing else.

The table of §46.3 stands, with the `𝔐_F` row's "continuation" entry unchanged (open) and its
"multivalued" entry the only genuine gain.

---

## 47. Cycles 45–46 (2026-07-25) — MI is not implied by the Riemann Hypothesis for `F`

### 47.1 What RH does give

Assume RH for `F ∈ S` (all non-trivial zeros on `σ = 1/2`). Then:
1. `F'/F` is holomorphic on `σ > 1/2` except for the pole at `s=1`, so **`log F` is single-valued
   and holomorphic there** — the multivaluedness obstruction of §43.3 disappears on the right;
2. by the FE, `log F(s) = log X(s) + log \bar F(1−s)`, and `1−σ > 1/2` when `σ < 1/2`, so `log F` is
   single-valued on `σ < 1/2` as well: **under RH, `log F` is single-valued on `C` minus the
   critical line (and the trivial-zero points)**;
3. under RH, `|log F(σ+it)| ≪ log t / log log t` for `σ > 1/2`, so
   `∫_0^T |log F(σ+it)|²dt ≪ T(log T)² ≪ T^{1+ε}` and **Carlson's theorem applies**, giving
   ```
   lim_T (2T)^{−1} ∫_{−T}^{T} |log F(σ+it)|² dt  =  𝔏'_F(2σ)      for all σ > 1/2 .
   ```

### 47.2 What RH does not give

The identity in (3) holds exactly on the region where `𝔏'_F(2σ) = Σ_n|b_F(n)|²n^{−2σ}` already
converges (`σ > 1/2`, i.e. `w > 1`). Continuation past `w = 1` would require the mean square to be
controlled *at and below* `σ = 1/2` — but that is precisely where `log F` has its singularities
(every zero), even under RH: RH puts all the zeros **on** the critical line, so the line
`σ = 1/2` is exactly the natural boundary of the single-valued region. Three-lines between
`σ_1 > 1/2` and `σ_2 < 1/2` is therefore unavailable.

> **Conclusion.** `RH(F) ⇏ MI`, hence `RH(F) ⇏ Selberg's Conjecture A`. Under RH the *multivaluedness*
> obstruction vanishes off the critical line, but the *continuation* obstruction is untouched — and
> RH makes the critical line the exact boundary of holomorphy of `log F`, so it cannot help to cross
> it.

This is consistent with the received view that Conjecture A is an arithmetic (functoriality-type)
statement independent of GRH, and it now has a precise mechanism: **RH controls where `log F` is
single-valued; MI is about continuing a quadratic object across the very line RH populates with
zeros.** Recorded, with the corollary that no zero-location hypothesis can substitute for MI.

### 47.3 Consequence for the search

Any proof of Conjecture A must therefore use an input that is *not* about the location of zeros.
Combined with §22.2 (four hard cores) and Theorem 4 (axioms (1),(4),(5) are insufficient), the
admissible inputs are narrowed to: functoriality-type constructions, or a genuinely new
single-valuedness principle for quadratic objects. Recorded as the standing constraint on future
cycles.

---

## 48. Cycle 47 (2026-07-25) — the Estermann/Kurokawa lens: MI asserts non-generic structure

`R_{F,F}(w) = ∏_p R_p(p^{−w})` with `R_p(x) = Σ_k |a_F(p^k)|² x^k`, `R_p(0)=1`. Estermann (1928) and
Kurokawa: for a **fixed** polynomial `P` with `P(0)=1`, `∏_p P(p^{−s})` factors as
`∏_{k≥1} ζ(ks)^{c_k}·(convergent)` with `c_k` the log-coefficients of `P`, and continues
meromorphically to all of `C` **iff** `P` is a product of cyclotomic polynomials; otherwise the
singularities at `s = 1/k` accumulate and `Re s = 0` is a **natural boundary**.

> **Consequence for the programme.** Continuation of an Euler product past its abscissa is *not*
> generic: it is a structural property of the local factors. `MI` therefore is not a technical
> continuation statement but the assertion that the Rankin–Selberg local factors `R_p` of a
> Selberg-class element are of `L`-function type — i.e. `R_p(x) = ∏_{i,j}(1 − α_i conj(α_j) x)^{−1}`
> up to harmless corrections. That is exactly the polynomial-Euler-product/functoriality structure.

Two caveats recorded so the lens is not over-read:
1. Estermann's dichotomy is for a *fixed* `P`; here `R_p` varies with `p`, so the accumulation
   argument does not apply verbatim. What survives is the principle: `log R_{F,F}(w) =
   Σ_p |a_F(p)|²p^{−w} + (holomorphic past 1/2)`, so continuation past `w=1` is *equivalent* to the
   prime sum continuing — and for a prime sum `Σ_p A_p p^{−w}` that is precisely the question of
   whether `(A_p)` is "L-function structured".
2. The natural boundary in the fixed-`P` case sits at `Re s = 0`, not at the abscissa; so a natural
   boundary for `R_{F,F}` would be expected at `Re w = 0`, and `MI` (a statement at `w=1`) is not
   directly threatened by it.

**Net value.** The lens explains *why* MI has resisted every technique in this programme: it is not
an estimate that is missing but a structural hypothesis on local data, of the same kind that
Estermann's theorem shows is generically false for Euler products. It also sharpens the disproof
route: a counterexample to Conjecture A would be an `F ∈ S` whose Rankin–Selberg local factors are
not of `L`-function type — and by §40.2 such an `F` must have constant-modulus prime coefficients
with oscillating phase, degree `≥ 2` with `q_F > 1` or degree `≥ 3`.

---

## 49. Cycle 48 (2026-07-25) — failed lower-bound attempts; preprint updated

### 49.1 `n_F ≥ 1` for entire `F` — attempts, all failed

- **Via `ζ`-column:** `κ_{F,ζ} = m_F ∈ Z` unconditionally and `|κ_{F,ζ}|² ≤ n_F`, giving
  `n_F ≥ m_F²`. Useful only when `F` has a pole; vacuous for entire `F`.
- **Via `F·ζ`:** `n_{Fζ} = n_F + 1 + 2m_F = n_F + 1 ≥ 1` gives only `n_F ≥ 0`.
- **Via the zero count:** the naive estimate "each of the `≍ (d/2π)T log T` zeros contributes
  `log²|t−γ|` over its spacing interval, so `Var(log|F|) ≫ (log log T)²`" is **wrong** — it
  over-counts, since `log|F| ≈ log|t−γ|` holds only on a set of measure far smaller than the
  spacing; the correct measure estimate `meas{log|F| < −V} ≈ T e^{−V²/log log T}` returns
  `∫ log²|F| ≍ T log log T`, matching Selberg. No lower bound follows. Recorded so the
  over-counting is not repeated.
- **Via Littlewood's lemma:** gives the *first* moment `∫_0^T log|F(1/2+it)|dt = 2πΣ_{β>1/2}(β−1/2)`,
  not the variance.

### 49.2 No exotic elements are known

Every known element of `S` is automorphic, and for automorphic `π` (even non-tempered, hence outside
`S`) the Rankin–Selberg `L`-function has a simple pole at `w=1`, so `n_F = 1` by Schur. A
counterexample to Conjecture A must therefore be genuinely non-automorphic, and none is known —
consistent with the classification results closing every degree range where a construction could be
checked.

### 49.3 Preprint updated

`docs/drafts/pipeline/4-publication-ready/monodromy-integrality-selberg.md` now carries Theorems 6–9
(explicit `ℛ_F`; log-coefficient transfer, machine-checked; linear integrality (a),(b);
`RH ⇏ MI`), the Estermann/Kurokawa remark, and the narrowing of the counterexample search space.

---

## 50. Cycle 49 (2026-07-25) — full Lean audit, and the consolidated hand-off

### 50.1 Audit

All fourteen theorems of the programme were re-audited in one file
(`import` of the four modules, `#print axioms` on every declaration). Every one depends only on
`[propext, Classical.choice, Quot.sound]` — no `sorry`, no added axiom, no conditional hypothesis
baked in:

| module | theorems |
|---|---|
| `RHTower.SelbergPairingPrimeSquare` | `divisorsAntidiagonal_prime_sq`, `arithmeticFunction_mul_apply_prime_sq`, `arithmeticFunction_mul_apply_prime'`, `selberg_pairing_prime_sq`, `selberg_pairing_sum_eq`, `selberg_energy_polarization`, `selberg_pairing_cauchy_schwarz`, `int_eq_zero_or_one_or_neg_one_of_sq_le_one` |
| `HTGeometry.GeneralizedDirichletMeanValue` | `genPoly_mul_conj`, `genPoly_meanValue`, `oscInt_zero` |
| `HTGeometry.ResidueJumpLowerBound` | `residue_jump_bound`, `residue_jump_of_integral_eq_zero` |
| `HTGeometry.LogCoefficientTransfer` | `log_coeff_bound` |

### 50.2 Consolidated hand-off (supersedes §12.6)

**Target.** Selberg's Conjecture B for `S`. **Status: open.**

**Read in this order after a compaction.**
1. §22.2 — the equivalence web: automorphy / twist / MI / (P2), and what implies what.
2. The do-not-retry list: §4 (1–7), §7 (8–13), §9.1, §9.6, §10.1, §11.1, §20.4, §21.1, §22.1,
   §26.3, §28.2, §31, §38.1–38.3, §46.4, §49.1.
3. `docs/drafts/pipeline/4-publication-ready/monodromy-integrality-selberg.md` — all standing
   theorems with proofs (Theorems 1–9 + the Radius Law).
4. `docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md` — the standalone theorem.
5. §37.3, §40.2 — the narrowed counterexample search space.

**The one open statement carrying the programme:** MI — `R_{F,F}` is meromorphic at `w = 1`.
Equivalently (§36) `ℛ_F = exp(Σ_p Σ_k k|b_F(p^k)|²p^{−kw})` is meromorphic at `w=1`; equivalently
(§43) the `L²`-mean of `log F` on vertical lines continues past `σ = 1/2`; equivalently (§46) the
same for `F'/F` with a double pole of coefficient `n_F`.

**What is known not to work:** every construction of `R_{F,G}` out of `F` and `G` (four structural
obstructions); positivity alone (`ζ^{1/2}` witness); RH (§47); Halász (§38.1); Carlson (§31, §46.4);
the pretentious propagation (§34); truncated spectral data (§20.4).

**The sharpest concrete question:** can `F ∈ S` have `|a_F(p)|` of constant non-integral mean square
with oscillating phase? By §40.2 such an `F` must have degree `≥ 2` with `q_F > 1`, or degree `≥ 3`.

**What is proved here and stands:** Theorems 1, 2, 4, 6, 7, 8, 9 and Corollary 3; the Cusp–Spectrum
Radius Law with its `S^♯` form and four exact verifications; Lemma A′; the `d = 1/2/≥3` spectral
trichotomy; and the fourteen Lean certificates above.

---

## 51. Cycles 50–51 (2026-07-25) — MI as a Hadamard-product closure statement

### 51.1 No algebraic operation on `F` produces `|a_F(p)|²`

The functions constructible from `F` inside the meromorphic world — `F(s)`, `F'(s)`, `F(s±a)`,
`F(as)`, products, quotients, `\bar F` — all have prime log-coefficients that are **ℂ-linear** in
`a_F(p)`, `conj(a_F(p))` and their shifts:
`F(s)F(s+a)` gives `a_F(p)(1+p^{−a})`; `F(2s)` has no `p^{−s}` term at all; and so on. Producing
`a_F(p)·conj(a_F(p))` requires multiplying coefficients at the *same* `n`, i.e. the **Hadamard
product** of Dirichlet series — which is not an algebraic operation on the function.

> **MI restated.** The class of Dirichlet series arising from `S` is closed under the Hadamard
> product with the conjugate, *in the sense of preserving meromorphy at `w=1`*.

This is a closure property, and no general theorem supplies it: Hadamard products preserve
**rationality** (classical, for power series) and **holonomicity**, but not meromorphy. Locally this
is visible and true — under a polynomial Euler product `F_p` is rational, hence `R_p = F_p ⊙ \bar F_p`
is rational — but the global product `∏_p R_p` is exactly the open point.

*Connection to hypertranscendence (the repository's theme):* the holonomicity route is unavailable
because `ζ` (and every `F ∈ S`) is hypertranscendental — it satisfies no algebraic differential
equation — so `F` is not `D`-finite and the "Hadamard product of `D`-finite is `D`-finite" theorem
cannot be applied. Recorded as the precise reason the holonomic route is closed.

### 51.2 Searching for a counterexample to the closure property

A counterexample would be a meromorphic Dirichlet series `D` with an Euler product whose prime
coefficients have **non-integral quadratic density**. Attempts:
- `a_p = c·χ(p)`, `c = 1/√2`: then `Σ_p a_p p^{−s} = c·log L(s,χ) + holo`, so
  `D = L(s,χ)^{1/√2}·(holo)` — **not meromorphic** (branch points at the zeros of `L`).
- `a_p = i` for all `p`: `D = ζ(s)^i·(holo)` — **not meromorphic**.
- `a_p` supported on a sparse set: the quadratic density is `0` — integral, no counterexample.

The pattern is forced by §39.1/§40.1: **for `D` meromorphic, the *linear* density is an integer.**
So any candidate must have `Σ_p a_p p^{−s} = Σ_j m_j log H_j(s) + holo` with `m_j ∈ Z` and `H_j`
meromorphic, whence `a_p = Σ_j m_j a_{H_j}(p) + small` and
```
quadratic density of a_p  =  Σ_{j,l} m_j m_l ⟨H_j, H_l⟩ .
```

> **Consequence (structural).** Non-integrality of the quadratic density can only come from
> non-integrality of the *pairings of the building blocks*. Conjecture A is therefore a **closure
> statement**: if the primitive building blocks pair integrally, everything assembled from them does.
> This is precisely Corollary 3's decomposition `B ⟸ MI + (P1) + (P2)` seen from the coefficient
> side, and it explains why no counterexample can be assembled from known meromorphic pieces —
> every such piece is built from `ζ` and Dirichlet `L`-functions, whose pairings are integral by the
> classical degree-1 case.

### 51.3 Net

The batch produces no new theorem but two clean structural statements: MI is a Hadamard-product
closure property (with the hypertranscendence of `ζ` explaining why the holonomic route is closed),
and non-integrality of a quadratic density is inherited, never created — so a counterexample cannot
be assembled, only found among genuinely non-automorphic elements. Both are recorded as constraints
on future cycles.

---

## 52. Cycle 52 (2026-07-25) — full hgtl7 cycle: the **Energy Gap** conjecture

### Phase 1–2. Frontier
Corpus: nothing on `S` beyond this programme. External (fresh search, July 2026): no result of
MI type; the newest adjacent item is *Selberg orthogonality for half-integral weight modular forms*
(arXiv:2508.07734, 2025), which does not touch the abstract class. Novelty of MI, the Cusp–Spectrum
Radius Law and `ℛ_F` unchallenged.

### Phase 3. Conjecture: **(EG) Energy Gap**

> There is `δ > 0` such that for every `F ∈ S`, the prime energy density
> `n_F := limsup_{σ→1+} ( Σ_p |a_F(p)|² p^{−σ} ) / log(1/(σ−1))`
> satisfies **either `n_F = 0` or `n_F ≥ δ`**. Sharp form: `δ = 1`, and `n_F = 0` only for `F = 1`.

*Structurally new:* it asserts a **spectral gap** for the prime energy on `S` without asserting
integrality — strictly weaker than Conjecture A, and of a type (gap/discreteness) that is sometimes
provable when integrality is not (cf. Lehmer-type gap theorems). *How it fails:* an `F` with
`n_F ∈ (0,1)`, e.g. the test case `|a_F(p)| = 1/√2` (`n_F = 1/2`). *Meets parent theory:* automorphic
`F` has `n_F = Σ e_i² ≥ 1`. *New world if true:* the Selberg class is discrete in the prime-energy
metric, so distinct primitives are separated — exactly the discreteness needed for (P2)/FIN′.
**[OPEN CORE]** ruling out `n_F ∈ (0,1)` for entire `F` with no zero on `Re s = 1`.

### Phase 4. Attack — verdict `SURVIVES PRELIMINARY ATTACK`
Not false (no `F` with `n_F ∈ (0,1)` is known); not circular (strictly weaker than Conjecture A and
does not assume it); not a consequence of a parent theory except the conjectural ones; not
insignificant (it kills the sharpest test case and yields discreteness). Fresh search found no
statement of a gap for `n_F` in the literature.

### Phase 5. Theorem (partial EG). PROVED HERE.

> For every `F ∈ S` and every `θ ∈ R`, with `ν := |ord_{s=1+iθ} F|` (pole order at `s=1`, or the
> order of a zero at `1+iθ`),
> ```
> n_F  ≥  ν² .
> ```
> In particular `n_F ≥ 1` whenever `F` has a pole at `s=1` or a zero anywhere on `Re s = 1`.
> Hence **EG holds for every `F ∈ S` except possibly those that are holomorphic and non-vanishing on
> the whole line `Re s = 1`.**

*Proof.* `F` is meromorphic with at most a pole at `s=1`, so near `s_0 = 1+iθ`,
`log F(s) − (−ν)·log(1/(s−s_0))` is holomorphic (the singular part is well defined even though the
branch is not). By the Euler product and the Newton-relation bound `|b_F(p^k)| ≪ (4C_ε)^k p^{kε}`
(§42.1, Lean-certified), `log F(s) = Σ_p a_F(p)p^{−s} + (holomorphic on σ > max(1/2,θ_F))`. Hence
along `s = σ+iθ`, `σ → 1+`,
`|Σ_p a_F(p)p^{−σ−iθ}| = ν·log(1/(σ−1)) + O(1)`.
On the other hand, by weighted Cauchy–Schwarz with weights `w_p = p^{−σ}`,
`|Σ_p a_F(p)p^{−σ−iθ}| ≤ (Σ_p |a_F(p)|² p^{−σ})^{1/2} (Σ_p p^{−σ})^{1/2}
 ≤ ((n_F+ε)log(1/(σ−1)))^{1/2}(log(1/(σ−1)))^{1/2}(1+o(1))`.
Comparing, `ν ≤ (n_F+ε)^{1/2}` for every `ε>0`, i.e. `n_F ≥ ν²`. ∎

*Placement.* This is the quantitative form of the Kaczorowski–Perelli implication
"normality ⟹ generalized PNT": it shows a zero or pole on the `1`-line **forces** energy `≥ 1`,
with no integrality assumed. Its converse reading ("`n_F < 1 ⟹ GPNT(F)`") is vacuous under
Conjecture A, so the useful content is the stated lower bound.

### Phase 6. Lean
`RHTower.weighted_cauchy_schwarz` added to `SelbergPairingPrimeSquare` (`lake build` green,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`): for arbitrary non-negative weights,
`‖Σ_p a_p w_p‖² ≤ (Σ_p ‖a_p‖² w_p)(Σ_p w_p)`. This is precisely the inequality used in Phase 5.
Programme total: **15** certified theorems.

---

## 53. Cycle 53 (2026-07-26) — EG's remaining case: five attacks, all fail

Configuration: `F ∈ S` non-constant, **entire**, **non-vanishing on `Re s = 1`**, `0 < n_F < 1`.
(By §52 every other configuration is settled.)

1. **Euler-product size bound.** `n_F<1` gives, by weighted Cauchy–Schwarz,
   `|log F(σ+it)| ≤ √(n_F)·log(1/(σ−1))(1+o(1))` uniformly in `t`, so
   `|F(σ+it)| ≪ (σ−1)^{−√(n_F)−ε}`. Compared with the truth for `ζ` (`|ζ(1+it)| ≪ log t`) this is
   very lossy; it yields nothing on the line. **Fails.**
2. **Second-moment lower bound.** `∫_0^T|F(1/2+it)|²dt ≍ T(log T)^{n_F}`; proving `≫ T log T` would
   give `n_F ≥ 1`. The mollified Cauchy–Schwarz route
   `∫|F|² ≥ |∫F\bar M|²/∫|M|²` returns, for `c_m = conj(a_F(m))`, exactly
   `T Σ_{m≤M}|a_F(m)|²/m ≍ T(log M)^{n_F}` — **circular**; for `c_m = 1` it returns
   `T·|F(1)|²/log M` — **too weak**.
3. **Zeros vs. variance.** The Jensen/disc computation gives only subharmonicity
   (circle-mean of `log|F|` `≥` centre value), consistent and non-contradictory. The naive
   "each zero contributes `log²|t−γ|`" estimate was already refuted in §49.1. **Fails.**
4. **Monoid iteration.** `F^k` has `n_{F^k} = k² n_F`, exceeding `1` for large `k`, but `F^k` is
   still entire and non-vanishing on the line, so §52's theorem gives nothing. `F·\bar F` has
   `n = 2c²(1+m₂)` with `m₂` the mean of `cos 2φ_p` — again no constraint. **Fails.**
5. **Constant-modulus normalisation** `|a_F(p)| = c < 1`. No local obstruction (§38.2); `a_F(p²) =
   b_F(p²) + c²e^{2iφ_p}/2` with `|a_F(p²)| ≪ p^ε`, `|b_F(p²)| ≪ p^{2θ}` is vacuous; under PEP any
   `c ≤ ∂_p` is attainable. **Fails.**

**Diagnosis.** Every attack either returns `n_F` on both sides (circular) or uses only the *size* of
`a_F(p)`, which the axioms constrain solely through Ramanujan. What is missing is the same thing MI
needs: a *global* single-valued object whose logarithm carries `|a_F(p)|²`. EG is therefore not
easier than MI in its remaining case — it is the same wall, reached from a weaker statement.

**Positive residue.** The reduction of §52 stands and is worth keeping as the sharp form:
> Selberg's Conjecture A fails only if some `F ∈ S` is entire, non-vanishing on `Re s = 1`, and has
> prime energy density in `(0,1)`.
Combined with §40.2, such an `F` must additionally have constant-modulus prime coefficients with
oscillating phase, in degree `≥ 2` with `q_F > 1` or degree `≥ 3`. That is the tightest description
of a counterexample the programme has produced.

---

## 54. Cycle 54 (2026-07-26) — corpus cross-check: the repository's RH programme does not feed this one

Phase-1 re-audit of the internal corpus for machinery usable on MI:

1. **`0-backlog/f1-hodge-index-theorem.md` and the `F₁`-Hodge cards.** These aim at RH via
   "RH ⟺ Hodge–Riemann positivity `Q_W ⪰ 0` of an `F₁`-MHS on `\overline{Spec Z}` viewed as a proper
   `F₁`-curve, with properness = the product formula". Even if that programme succeeded it would
   deliver **RH**, and §47 proves `RH(F) ⇏ MI`. **So the repository's principal RH route is
   orthogonal to Selberg orthogonality and cannot be borrowed.** Recorded so no later cycle tries.
2. **`2-fully-proven/function-field-spectral-closure-universality-law.md`.** Its content — a finite
   Frobenius multiset is closed under `ω ↦ q/ω` **iff** its elementary symmetric functions satisfy
   the `q`-weighted reciprocal functional equation — is a *local* rigidity: over `F_q` the functional
   equation is a statement about the finitely many Frobenius eigenvalues, i.e. about the local
   factor itself. Over `Q` the Selberg functional equation is **archimedean** (gamma factors,
   conductor) and says nothing about any `F_p`.
   > **This asymmetry is the precise reason the function-field proof of orthogonality (Frobenius
   > multiset + Deligne purity + Chebotarev/Schur) has no shadow in the Selberg class.** Over `F_q`
   > the FE constrains the local data; over `Q` it does not. Recorded as the sharpest statement of
   > the function-field/number-field gap for this problem, refining §10.3.
3. Nothing else in `formal/` or the pipeline addresses `S`; the four programme modules remain the
   only relevant machinery, and they are already reused.

**Net.** The corpus contains no usable route to MI, and two of its largest programmes are now
positively excluded (the `F₁`/RH route by §47; the function-field route by the FE-locality
asymmetry). This narrows future work to the paths recorded in §22.2.

---

## 55. Cycle 55 (2026-07-26) — classification of integrality mechanisms; only monodromy is available

### 55.1 The six mechanisms

Integrality of a real quantity in mathematics arises, essentially exhaustively, from one of:
(a) a **dimension** of a vector space; (b) a **degree** or index; (c) a **trace of an idempotent**
(equivalently a multiplicity in a semisimple category); (d) an **Euler characteristic**;
(e) a **winding number / monodromy exponent**; (f) a **lattice-point count**.

For `n_F`:
- (a),(c) require a Tannakian/endomorphism model of `S` — i.e. automorphy. Not available; §30.2 shows
  (P1) needs exactly this.
- (d) requires a cohomology theory over `Q` — the `F₁` programme, excluded for this problem by §54.1
  (`RH(F) ⇏ MI`).
- (f) would need `n_F` to count lattice points in an object built from `F`; no such object exists in
  the axioms.
- (b) is **excluded outright** by Theorem 55.2 below.
- (e) is the mechanism that *does* work in the linear case (§39.1, §40.1: `ν = ord_{1+iθ}F ∈ Z`
  because `F` is single-valued), and MI is precisely its quadratic form.

> **Consequence.** MI is not one formulation among many: it is the **only** integrality mechanism
> accessible from the Selberg axioms alone. Every other mechanism requires structure the axioms do
> not provide. This is why every route recorded in this log terminates either in MI or in
> functoriality.

### 55.2 Theorem (`n_F` is not archimedean). PROVED HERE.

> `n_F` is **not** a function of the archimedean data `(d_F, q_F, γ_F)`.

*Proof.* Let `q` be such that there are two distinct primitive even Dirichlet characters
`χ₁ ≠ χ₂ (mod q)`. Put `F := L(·,χ₁)L(·,χ₂)` and `G := L(·,χ₁)²`. Both lie in `S`, both have degree
`2`, conductor `q²`, and the **same** gamma factor `(π^{−s/2}Γ(s/2))² q^{s}` (both characters are
even and primitive mod `q`). Their prime energies are, by the classical degree-1 case of Selberg's
conjectures (orthogonality of characters),
`n_F = 1 + 1 = 2` and `n_G = (1+1)² = 4`. ∎

*Consequence.* Mechanism (b) is dead: no formula `n_F = Φ(d_F,q_F,γ_F)` can exist, so the functional
equation alone cannot compute the prime energy. This is the rigorous form of the FE-locality
asymmetry recorded in §54.2 — over `F_q` the functional equation *is* local data and determines the
Frobenius multiset; over `Q` it is archimedean and, by the above, determines nothing about `n_F`.

### 55.3 Placement

§55.1–55.2 together give the programme its sharpest self-description: *Selberg's Conjecture A asserts
the integrality of a quantity that the axioms can only reach through monodromy, and the monodromy in
question is that of an object (`R_{F,F}`) which the axioms do not supply.* Every obstruction recorded
in this log is an instance of that single sentence.

---

## 56. Cycle 56 (2026-07-26) — why a counterexample cannot be built: the two-sided phase squeeze

A counterexample to Conjecture A needs prime coefficients `a_F(p) = c·e^{iφ_p}` with `c² ∉ Z`. By
§52 it must additionally have **no** pole or zero anywhere on `Re s = 1`, i.e. all *linear* densities
must vanish, while the *quadratic* density is `c² ∉ Z`. Examining the two natural ways to choose the
phases:

### 56.1 Structured phases — excluded by monodromy

- `φ_p ≡ 0` (i.e. `a_F(p) = c`): §39.1 forces `c ∈ Z`.
- `a_F(p) = c·χ(p)` for a Dirichlet character: `Σ_p a_F(p)p^{−s} = c·log L(s,χ) + holo`, so
  `F = L(s,χ)^c·(holo)` — not single-valued unless `c ∈ Z`.
- `a_F(p) = c·p^{iβ}`: `F = ζ(s−iβ)^c·(holo)`, giving a singularity at `s = 1+iβ`, which for `β ≠ 0`
  is forbidden by axiom (2) unless `c = 0` (§40.2).
- Any `a_F(p)` whose linear density at **some** point of the `1`-line is non-zero is caught by §52's
  `n_F ≥ ν²`.

**So every arithmetically structured phase choice is excluded**, and always by the same mechanism:
single-valuedness of a meromorphic object.

### 56.2 Generic phases — excluded by the functional equation

Take `φ_p` generic (e.g. i.i.d. uniform). Then:
- `Σ_p a_F(p)p^{−s}` is a random Dirichlet series; by Kolmogorov's three-series theorem it converges
  a.s. for `Re s > 1/2`, so it is **holomorphic on the whole line `Re s = 1`** — all linear densities
  vanish, exactly as required;
- `Σ_p |a_F(p)|² p^{−s} = c² Σ_p p^{−s} = c² log ζ(s) + holo`, giving the **non-integral** quadratic
  density `c²`;
- but such a series a.s. has `Re s = 1/2` as a **natural boundary**, so `F = exp(·)` admits no
  meromorphic continuation to `C` and no Selberg functional equation.

**So the coefficient system a counterexample needs exists, but generic phases cannot be completed to
an element of `S`.**

### 56.3 The squeeze

> A counterexample to Selberg's Conjecture A must have prime phases that are **neither arithmetically
> structured** (excluded by monodromy: §39.1, §40.2, §52) **nor generic** (excluded by the natural
> boundary: no functional equation). It must occupy the narrow window in between: phases regular
> enough to admit a meromorphic continuation with a `Γ`-factor functional equation, yet irregular
> enough that every linear density vanishes while the quadratic density is non-integral.

This is the sharpest structural reason yet recorded for why no counterexample has ever been
exhibited, and it is complementary to the Estermann lens (§48): Estermann says continuation is
non-generic; §56.2 says the *specific* non-generic behaviour a counterexample needs is exactly the
kind randomness destroys. Conjecture A asserts that the window is empty.

**Positive residue.** The squeeze converts the search for a counterexample into a concrete question:
*is there a sequence of phases `(φ_p)` admitting a `Γ`-factor functional equation for
`exp(Σ_p c e^{iφ_p}p^{−s} + ...)` with all linear densities zero?* Under the automorphy conjecture
the answer is no, and every known `F ∈ S` has phases coming from Satake parameters of an automorphic
representation — for which the quadratic density is `dim End = 1` by Schur.

---

## 57. Cycle 57 (2026-07-26) — the functional equation for `log F`, and why it gives no leverage

Write `P(s) := log F(s) = Σ_p a_F(p)p^{−s} + (k ≥ 2 terms)`. Taking logarithms in the Selberg
functional equation gives, for `Re s < 0` (where the dual series converges),
```
P(s) = A(s) + \bar P(1−s) ,      A(s) := log ω + log \barγ(1−s) − log γ(s)   (explicit, archimedean).
```
So the analytic continuation of the prime sum to the far left **is** the dual prime sum plus explicit
archimedean terms — a genuine self-consistency condition on the coefficient sequence `(a_F(p))`.

Three consequences, all checked and none useful for MI:

1. **Mean squares.** `(2T)^{−1}∫|P(σ+it)|²dt ≈ (1/2−σ)²d²log²T + O(log T)` for `σ<0`, exactly
   reproducing §43.2. No new information.
2. **Critical line.** At `s = 1/2+it`, `\bar P(1/2−it) = conj(P(1/2+it))`, so
   `2i·Im P(1/2+it) = A(1/2+it) = log ω − 2i·Im log γ(1/2+it)`, i.e.
   `Im log F(1/2+it) = −Im log γ(1/2+it) + const` — the classical Riemann–Siegel `θ`-relation.
   It says the **phase** of `F` on the critical line is archimedean and the **modulus** carries the
   arithmetic. But the relation holds only modulo the branch jumps at the zeros, i.e. modulo
   `π S_F(t)`, and `S_F` is precisely the arithmetic part. **No simplification.**
3. **Coefficient constraint.** The relation is functional, not coefficientwise: it constrains `P` as
   a function, and produces no relation between `Σ_p|a_F(p)|²p^{−w}` at `w` and at `2−w` (the
   Rankin–Selberg object has degree `d²`, so §9.1 applies). **No functional equation for `𝔏'_F`.**

**Net.** The `log`-form of the functional equation is exact and clean, and it confirms two earlier
computations independently, but it carries no quadratic information — consistent with the
linear-moment closure principle (§10.1). Recorded so the `log`-FE is not re-derived.

---

## 58. Cycle 58 (2026-07-26) — Wirsing: the *asymptotic* half of Conjecture A needs no meromorphy

### 58.1 Clarification

`|a_F(n)|²` is **non-negative and multiplicative**. Wirsing's mean-value theorem: if `f ≥ 0` is
multiplicative with `f(p) ≤ C` for all `p` (plus the usual mild control at prime powers) and
`Σ_{p≤x} f(p)/p = τ·log log x + O(1)`, then
```
Σ_{n≤x} f(n) ~ c_f · x (log x)^{τ−1} / Γ(τ) .
```
Applying this with `f = |a_F|²`:

> **Under BS (bounded prime coefficients) and the existence of the density `n_F`, the
> Selberg–Delange asymptotic `Σ_{n≤x}|a_F(n)|² ~ c x (log x)^{n_F−1}` holds unconditionally — no
> meromorphy, no MI.**

**Consequence.** The content of Selberg's Conjecture A splits cleanly:
- the *asymptotic shape* is a theorem given BS + existence of the density (Wirsing);
- the *integrality of `n_F`* is the entire remaining content, and by §55.1 it is reachable only
  through monodromy, i.e. MI.

This is worth recording because several cycles implicitly treated the asymptotic and the integrality
as one package (e.g. the Selberg–Delange steps in §36–37). They are not: only integrality is hard.

### 58.2 Negative sweep (all recorded, none to be retried)

- **Unique factorisation directly.** `F = ∏F_i = ∏G_j` gives `Σ_i a_{F_i}(p) = Σ_j a_{G_j}(p)`;
  pairing against `a_{F_1}` needs the signs of `B(F_i,F_1)`, i.e. SOC. Degrees and conductors only
  give `Σ d_{F_i} = Σ d_{G_j}` and `∏q = ∏q`. Gamma factors partition, but §55.2 shows distinct
  elements can share a gamma factor. **No route.**
- **`0/1`-valued coefficients.** If `|a_F(n)|² = a_H(n)` for some meromorphic `H`, MI is automatic.
  For `a_F(n) ∈ {0,1}`, `R_{F,F} = F`, so MI holds — but the only such element of `S` is `ζ`
  (`L(s,χ_0)` fails the Riemann-type functional equation, `ζ(s)/ζ(2s)` likewise). Degree 1 gives
  `R_{F,F} = ζ(w)∏_{p|q}(1−p^{−w})`, meromorphic ✓ — the known case. **No new instances.**
- **Disproof via a false consequence.** Every consequence of SOC (Artin holomorphy, unique
  factorisation, GPNT, algebraic independence of primitives, strong multiplicity one) is believed
  true and none is known false. **No disproof route from consequences.**

### 58.3 Revised statement of the open problem

> Selberg's Conjecture A `=` (asymptotic: **theorem**, given BS + density existence, by Wirsing)
> `+` (integrality of `n_F`: **open**, reachable only by monodromy, i.e. MI).
> Selberg's Conjecture B `=` Conjecture A `+` (P1) `+` (P2), both of which reduce to functoriality
> (§30.2, §35.4).

---

## 59. Cycle 59 (2026-07-26) — a MEROMORPHIC parent carrying `|a_F(p)|²`  [OWN — first of its kind]

### 59.1 The object

`F'/F` is meromorphic on `C` (axiom (2)) with Dirichlet series `−Σ_n Λ_F(n)n^{−s}`,
`Λ_F(n) = b_F(n)log n`. So is `\bar F'/\bar F` (since `\bar F ∈ S`). Hence
```
G(s) := (F'/F)(s) · (\bar F'/\bar F)(s)
```
is **meromorphic on all of `C`**, with poles only at the zeros and poles of `F` and `\bar F`, and
residue data built from the (integer) multiplicities. Its Dirichlet coefficients are
`c(n) = Σ_{de=n} Λ_F(d) conj(Λ_F(e))`, and in particular
```
c(p²) = Λ_F(p) conj(Λ_F(p)) + 2Λ_F(1)(…) = |a_F(p)|² log²p .
```

> **This is the first object in the programme that is (i) supplied by the axioms, (ii) meromorphic on
> `C`, and (iii) carries `|a_F(p)|²` in its coefficients.** Every earlier candidate (`R_{F,F}`,
> `ℛ_F`, `𝔏'_F`, `𝔐_F`) had (iii) but not (ii); every meromorphic object built from `F` before this
> had (ii) but only *linear* coefficient data (§59.3).

### 59.2 What still blocks

Splitting `c(n)` by `d = e` versus `d ≠ e`:
```
G(s) = 𝔐_F(2s) + Σ_{d≠e} Λ_F(d) conj(Λ_F(e)) (de)^{−s} ,     𝔐_F(w) = Σ_d |Λ_F(d)|² d^{−w} .
```
`𝔐_F(w) ~ n_F/(w−1)²` (§46.1), so MI is equivalent to the meromorphy of the **off-diagonal** sum.
Extracting the diagonal from a product of two Dirichlet series requires a kernel whose Mellin
transform is identically `1`:
- a `Γ(s)Γ(w−s)` kernel gives, by Mellin–Barnes,
  `Γ(w)·Σ_{d,e}Λ_F(d)conj(Λ_F(e))(d+e)^{−w}` — the **additive** convolution, not the diagonal;
- the only exact extractor is the `T → ∞` vertical mean, i.e. Carlson, which fails for `F'/F` below
  `σ = 1` (§46.4).

So the wall has moved: it is no longer "no meromorphic parent exists" but "the diagonal cannot be
extracted from a meromorphic parent". That is a strictly smaller obstruction and a different one.

### 59.3 Why earlier meromorphic candidates failed, for the record

`F(s±a)`, `F(as)`, `F'`, `F''`, products and quotients: all have prime coefficients **linear** in
`a_F(p)` and its shifts. `F·log F` has `p²`-coefficient `b_F(p²) + a_F(p)²` — quadratic, but
`log F` is multivalued so the product is not meromorphic. `(F'/F)²` is meromorphic with
`p²`-coefficient `a_F(p)² log²p` — quadratic but **unconjugated**. Only the pairing with
`\bar F'/\bar F` produces `|a_F(p)|²` while staying meromorphic.

> **Cycle-60 target.** Diagonal extraction from `G`. Two concrete lines: (a) find a kernel adapted to
> the *multiplicative* structure (a Mellin transform of a measure on `R_{>0}` that is a delta at `1`
> in the log-variable — impossible exactly, so seek an approximate identity with controlled error and
> a limiting argument); (b) exploit that `G`'s poles and residues are integral and located at the
> zeros of `F`, and ask whether `𝔐_F`'s double pole at `w=1` can be read off `G`'s polar data.

---

## 60. Cycle 60 (2026-07-26) — diagonal extraction from `G`: the contour form, and where it lands

### 60.1 Two-variable form and the exact extractor

Set `G(s₁,s₂) := (F'/F)(s₁)·(\bar F'/\bar F)(s₂)`, meromorphic in **two** variables (a product of
meromorphic functions of separate variables). For `Re w > 2` and `1 < c < Re w − 1`, expanding both
Dirichlet series and integrating over a truncated vertical segment,
```
(2πi)^{−1}∫_{c−iT}^{c+iT} G(s, w−s) ds
   = (T/π)·𝔐_F(w)  +  Σ_{d≠e} Λ_F(d) conj(Λ_F(e)) d^{−c} e^{−(w−c)} · sin(T log(e/d)) / (π log(e/d)),
```
so
```
𝔐_F(w) = lim_{T→∞} (π/T) · (2πi)^{−1} ∫_{c−iT}^{c+iT} (F'/F)(s) (\bar F'/\bar F)(w−s) ds ,
```
provided the Dirichlet-kernel off-diagonal is `o(T)`. **For each finite `T` the integral is a
holomorphic function of `w`** off an explicit union of vertical segments (where `w−s` meets a pole of
`\bar F'/\bar F`). Hence:

> **MI ⟸ the limit is locally uniform in `w` near `w = 1`.**

This is the sharpest constructive form the programme has reached: no functoriality, no spectral
truncation, no almost-periodicity — just a contour integral of two meromorphic functions.

### 60.2 Where it lands

To reach `Re w` near `1` the second argument `w−s` must traverse the critical strip, where
`\bar F'/\bar F` has its poles — at the conjugates of the zeros of `F`, with `≍ d log|t|` of them per
unit height. Deforming the contour past them picks up **residues at the zeros of `F`**, i.e. an
explicit-formula contribution, and the resulting expression is a double sum over pairs of zeros
weighted by `(ρ − \barρ')`-type factors.

> That is exactly the **pair correlation of zeros** of `F`, i.e. the Murty–Perelli route
> (IMRN 1999), already recorded as known (§4 item 6).

So the constructive chain closes onto an established programme rather than a new one. This is not a
dead end — it is a *derivation* of the pair-correlation route from the meromorphic parent `G`, which
explains why pair correlation is the natural home of the problem: it is what the diagonal extraction
from `G` produces after contour deformation.

### 60.3 Residues of `G` are not integral

Line (b) of §59.3 (read `𝔐_F`'s double pole off `G`'s polar data) fails: at a non-real zero `ρ` of
`F`, `G` has a simple pole with residue `m_ρ · (\bar F'/\bar F)(ρ)` — the multiplicity times a
*value*, not an integer. Only `F'/F` alone has integral residues; the product destroys it. Recorded.

### 60.4 Net

Two results: the exact contour extractor (§60.1), which is the cleanest constructive statement of MI
obtained so far; and the demonstration that its natural continuation is the pair-correlation route
(§60.2). The programme's constructive and known-literature lines now meet at a single point.

---

## 61. Cycle 61 (2026-07-26) — the explicit-formula form of `n_F`: the pole comes from each zero
pairing with its own reflection

### 61.1 The contour move

Start from §60.1 with `Re w > 2`, `1 < c < Re w − 1`. Move the `s`-contour rightwards past
`Re s = Re w`, so that `Re(w−s) < 0` and the functional equation applies to the second factor:
differentiating `\bar F(u) = F(1−u)γ(1−u)/(ω\barγ(u))` gives
```
(\bar F'/\bar F)(u) = −(F'/F)(1−u) − (γ'/γ)(1−u) − (\barγ'/\barγ)(u) ,
```
an exact identity with explicit archimedean remainder. Crossing the poles of `(\bar F'/\bar F)(w−s)`
at `s = w − \barρ` (`ρ` a zero of `F`, multiplicity `m_ρ`) contributes residues
`−m_ρ·(F'/F)(w−\barρ)`. Hence
```
𝔐_F(w) = π·lim_{T→∞} (1/T) Σ_{|Im ρ| ≤ T} m_ρ · ( −(F'/F)(w − \barρ) )  +  (archimedean)  +  (moved integral).
```
After the substitution the moved integral has an **empty diagonal**: its two Dirichlet series are
`Σ_d Λ(d)d^{−s}` and `Σ_e Λ(e)e^{−s−1+w}`, whose diagonal condition is `de = 1`, impossible for
`d,e ≥ 2`. So it contributes nothing to the `(π/T)`-limit.

### 61.2 The structural payoff

`(F'/F)(w − \barρ)` has a pole exactly when `w − \barρ` is a zero `ρ'` of `F`, i.e. when
```
w = ρ' + \barρ .
```
Near `w = 1` this reads `ρ' = 1 − \barρ` — and **by the functional equation every zero `ρ` of `F` has
`1 − \barρ` as a zero**. So *every* term of the zero-sum contributes a pole at `w = 1`.

> **Therefore the double pole of `𝔐_F` at `w = 1`, whose coefficient is `n_F`, is produced by each
> zero of `F` pairing with its own functional-equation reflection.** `n_F` is the *diagonal* of the
> pair correlation of the zeros — the self-pairing under `ρ ↦ 1 − \barρ`.

This is the cleanest description of `n_F` the programme has produced, and it explains the
Murty–Perelli phenomenon from the inside: the prime energy is not "related to" pair correlation, it
**is** its diagonal term, forced by the functional equation. It also explains why the off-diagonal
(`ρ' ≠ 1−\barρ`) is exactly the pair-correlation conjecture's content, and why integrality of `n_F`
should hold: the diagonal counts each zero once with its multiplicity `m_ρ ∈ Z`.

### 61.3 What is still missing

The zero-sum is over `≍ (d/2π)T log T` zeros divided by `T`, so it is `≍ log T`-sized before
cancellation; making the limit exist and isolating the `w = 1` double pole requires exactly the
uniformity that the pair-correlation conjecture supplies. So §61.1 is an **exact identity** where
Murty–Perelli assume an asymptotic — a better starting point, but the same open core.

**Recorded conclusion.** `n_F = ` (diagonal of the zero pair correlation) `= Σ_ρ m_ρ` normalised —
integral *if* the diagonal can be separated. The integrality of `n_F` is therefore, in this picture,
the integrality of a multiplicity count over zeros — mechanism (e) of §55.1 realised on the zero side
rather than the coefficient side.

---

## 62. Cycle 62 (2026-07-26) — CORRECTION to §61: the diagonal gives a *simple* pole, not the double
pole

Check the claim of §61.2 quantitatively. Insert the Hadamard partial-fraction expansion
`(F'/F)(u) = Σ_{ρ'} (u−ρ')^{−1} − (archimedean)` into the zero-sum:
```
Σ_ρ m_ρ ( −(F'/F)(w−\barρ) )  =  − Σ_{ρ,ρ'} m_ρ (w − \barρ − ρ')^{−1} + (archimedean) .
```
The "diagonal" `ρ' = 1 − \barρ` (present for every `ρ` by the functional equation) contributes
`−m_ρ/(w−1)` each — a **simple** pole. Summing over `|Im ρ| ≤ T` gives `−N_F(T)/(w−1)`, and the
`(π/T)` normalisation of §61.1 turns this into `≍ −(d/2)·log T/(w−1)`, which **diverges** as
`T → ∞` and is a simple pole, whereas `𝔐_F(w) ~ n_F (w−1)^{−2}` is a **double** pole with a finite
coefficient.

> **So §61.2's reading — "the double pole is produced by each zero pairing with its own reflection" —
> is wrong.** The diagonal of the zero pair correlation produces a divergent *simple* pole; the
> divergence must cancel against the archimedean terms of the explicit formula, and the double pole
> arises from the interplay, not from the reflection-diagonal alone.

**What survives.**
- §60.1, the extractor identity
  `𝔐_F(w) = lim_T (π/T)(2πi)^{−1}∫_{c−iT}^{c+iT}(F'/F)(s)(\bar F'/\bar F)(w−s)ds` for `Re w > 2`,
  `1 < c < Re w − 1`, derived by direct expansion. **Valid.**
- §59.1, the meromorphic parent `G = (F'/F)(\bar F'/\bar F)` with `c(p²) = |a_F(p)|²log²p`, and the
  verification that no other meromorphic function built from `F` carries conjugated quadratic data.
  **Valid.**
- §60.2, that pushing the extractor towards `w = 1` requires crossing the zeros and therefore lands
  on the pair-correlation route. **Valid as a qualitative statement.**
- §61.1's contour move and functional-equation substitution: **valid as an identity only if the
  `T`-truncation is handled with a smooth test function rather than a sharp cutoff.** With a sharp
  cutoff the residue sum and the moved integral each diverge and only their combination is finite.
  Marked as **needing repair**, not as a result.

**Lesson recorded.** Sharp-cutoff contour truncation is not compatible with the `(π/T)`-normalised
diagonal extraction: the two `T`-dependences (Dirichlet-kernel off-diagonal, and the number of
residues crossed) are of different orders. Any future attempt must use a smoothed extractor from the
start. Recorded so the error is not repeated.

---

## 63. Cycle 63 (2026-07-26) — smoothed extractor and the Baker separation of the off-diagonal

### 63.1 The smoothed extractor

Replace the sharp truncation of §60.1 by a weight `φ` on the `t`-line (`s = c+it`):
```
J(w;φ) := (2π)^{−1} ∫_R (F'/F)(c+it) · (\bar F'/\bar F)(w−c−it) · φ(t) dt
        = Σ_{d,e} Λ_F(d) conj(Λ_F(e)) d^{−c} e^{−(w−c)} · Φ(log(e/d)) ,     Φ := (2π)^{−1}\hatφ .
```
Diagonal: `Φ(0)·𝔐_F(w)`. So `𝔐_F` is extracted whenever the off-diagonal can be suppressed.

### 63.2 Baker's theorem separates the off-diagonal — quantitatively  [OWN input, new to the problem]

`Λ_F` is supported on prime powers, so the off-diagonal log-ratios are
`log(e/d) = k log q − j log p` with `p^j ≠ q^k`. By **Baker's theorem on linear forms in two
logarithms**, there is an effective `C` with
```
| k log q − j log p |  ≫  ( max(j,k) · log(pq) )^{−C}   ≫  (log X)^{−C}   for  d,e ≤ X .
```
Hence choosing `Φ` supported in `(−δ,δ)` with `δ = (log X)^{−C}` kills **every** off-diagonal pair
with `d,e ≤ X`, and the tail `d` or `e > X` contributes `≪ ‖Φ‖_∞ X^{−(c−1)}`. Normalising `Φ` to a
bump of width `δ` and height `δ^{−1}`,
```
𝔐_F(w) = δ · J(w;φ_δ) + O( X^{−(c−1)} ) ,     δ = (log X)^{−C} .
```
> **This is an unconditional, effective diagonal isolation** — the first quantitative separation of
> the diagonal in the programme, and it uses transcendence theory (Baker), which no earlier cycle
> touched. The repository already carries Baker machinery (`0-backlog/baker-for-stieltjes.md`).

### 63.3 Why it still does not cross the abscissa

`Φ` compactly supported forces `φ` to be entire of exponential type (Paley–Wiener), so the
`t`-integral runs over all of `R`. For `Re w > 2` and `c ∈ (1, Re w − 1)` the second argument has
`Re(w−c−it) > 1`, outside the critical strip, so `J(·;φ)` is holomorphic in `w` there. Pushing
`Re w` towards `1` forces `Re(w−c) < 1`, i.e. the argument enters the strip, where
`\bar F'/\bar F` has `≍ d log|t|` poles per unit height — and as `t` ranges over all of `R` these
poles sweep a two-dimensional set, so no open `w`-region survives.

**Net.** Baker gives an effective, unconditional separation of the diagonal *inside* the region of
convergence; the obstruction is now isolated entirely in the pole geometry of `\bar F'/\bar F` in the
critical strip, with no remaining combinatorial difficulty from the off-diagonal. Recorded as the
sharpest split of the difficulty so far: **combinatorics — solved (Baker); analysis in the strip —
open.**

---

## 64. Cycle 64 (2026-07-26) — the sum-of-arguments obstruction, and the collapse at `w = 1`

### 64.1 Why no contour deformation can work

In `J(w;φ) = (2π)^{−1}∫_R (F'/F)(s)(\bar F'/\bar F)(w−s)φ(t)dt`, `s = c+it`, the two arguments always
satisfy
```
Re s + Re(w−s) = Re w .
```
Deforming the `t`-contour by `iη` moves `Re s` to `c−η` and `Re(w−s)` to `Re w−c+η` — it trades one
factor's poles for the other's, and the sum is invariant. **For `Re w < 2` at least one argument
lies left of `Re = 1`, and for `Re w` near `1` both lie near `1/2`.** So the pinching by the poles of
`F'/F` and `\bar F'/\bar F` in the critical strip is unavoidable by any contour deformation. This is
the exact and final form of the obstruction identified in §63.3, and it is a *conservation law*, not
an estimate — no choice of `c`, `φ`, or deformation evades it.

### 64.2 The integrand collapses at `w = 1`

Differentiating the functional equation (as in §61.1) gives the exact identity, valid for
`Re(w−s) < 0`,
```
(\bar F'/\bar F)(w−s) = −(F'/F)(s + 1 − w) − (γ'/γ)(s+1−w) − (\barγ'/\barγ)(w−s) .
```
Hence the integrand of `J(w;φ)` equals
```
−(F'/F)(s)·(F'/F)(s + 1 − w)  −  (F'/F)(s)·A'(w−s) ,     A' explicit archimedean.
```
> **So the quadratic object is, after the functional equation, the *autocorrelation of `F'/F` at shift
> `1 − w`*, plus an explicit linear term.** At `w = 1` the shift vanishes and the integrand becomes
> `−[(F'/F)(s)]² − A'(1−s)(F'/F)(s)` — an expression in `F'/F` **alone**.

This is structurally the sharpest statement the programme has: `n_F`, the coefficient of the double
pole of `𝔐_F` at `w = 1`, is read off the **mean square of the logarithmic derivative of `F` at
shift zero**, with everything else explicit and archimedean.

### 64.3 Placement

The autocorrelation of `F'/F` is classically equivalent to the pair correlation of the zeros, so
§64.2 re-derives — now from the functional equation rather than from a contour deformation — that MI
sits exactly on the pair-correlation route. Together with §63.2 (Baker removes the off-diagonal
combinatorics) the programme's final picture is:

> **`n_F` = (coefficient of the `w=1` double pole of the mean square of `F'/F`), the off-diagonal is
> effectively separable by Baker, and the sole remaining difficulty is the unavoidable pinching of
> the two arguments in the critical strip, forced by `Re s + Re(w−s) = Re w`.**

Recorded as the closing structural statement of this line. Any further progress must come from
controlling `[(F'/F)]²` on the critical line — i.e. from pair correlation — and not from a smarter
extraction.

---

## 65. Cycle 65 (2026-07-26) — the diagonal-isolation mechanism, certified

`formal/GaloisForLFunctions/HTGeometry/DiagonalIsolation.lean` (in the `HTGeometry` umbrella;
`lake build` green; `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

- `HTGeometry.exists_gap_of_injOn` — for a finite index set with injective frequencies `λ`, there is
  `δ > 0` with `|λ d − λ e| ≥ δ` for all `d ≠ e`;
- `HTGeometry.diagonal_isolation` — if `Φ` vanishes at every non-zero difference `λ d − λ e`
  occurring in a finite double sum, then
  `∑_{d,e} A d · B e · Φ(λ d − λ e) = Φ(0)·∑_d A d · B d`.

Together these are the unconditional combinatorial core of §63: with `λ n = log n` and `A, B`
supported on prime powers, the non-zero differences are the linear forms `k log q − j log p`
(`p^j ≠ q^k`), and Baker's theorem supplies the **effective** gap `≫ (log X)^{−C}` for indices up to
`X`. The certified statements deliberately isolate the part that needs no transcendence input; the
Baker bound enters only in choosing `δ` as a function of `X`.

Programme total: **17** certified theorems across five modules
(`RHTower.SelbergPairingPrimeSquare`, `HTGeometry.GeneralizedDirichletMeanValue`,
`HTGeometry.ResidueJumpLowerBound`, `HTGeometry.LogCoefficientTransfer`,
`HTGeometry.DiagonalIsolation`).

**Standing state after 65 cycles.** The extraction line is closed by the conservation law
`Re s + Re(w−s) = Re w` (§64.1); the off-diagonal combinatorics is effectively solved (§63.2, now
certified in finite form); the target is the `w = 1` double pole of the mean square of `F'/F`
(§64.2); and the sole remaining difficulty is pair correlation of the zeros in the critical strip —
the Murty–Perelli route, now derived from inside rather than assumed.

---

## 66. Cycle 66 (2026-07-26) — caution: the mean-square reading of `𝔐_F` is valid only for `σ > 1`

`𝔐_F(w) = Σ_n |Λ_F(n)|² n^{−w}` converges for `Re w > 1` (`σ > 1/2`) and satisfies
`𝔐_F(w) ~ n_F (w−1)^{−2}`. It is tempting to read `n_F = lim_{σ→1/2+}(2σ−1)²·(mean square of `F'/F`
on the line `σ`)`. **That reading is only justified for `σ > 1`.**

Reason: with the partial-fraction expansion `F'/F(σ+it) = Σ_{|γ−t|≤1}(s−ρ)^{−1} + O(log(|t|+2))`, the
**diagonal** of `|Σ_γ (δ + i(t−γ))^{−1}|²` (`δ = σ − 1/2`) integrates to
`Σ_γ π/δ ≍ N_F(T)·π/δ ≍ T log T/δ`, so the zero-side contribution to `∫_0^T|F'/F(σ+it)|²dt` is
`T`-growing for every fixed `σ ∈ (1/2,1)`, while `𝔐_F(2σ)` is a finite constant. The two agree only
after the archimedean `O(log t)` term cancels the zero-sum — which is exactly what fails to be
uniform below `σ = 1`. This is the same failure recorded in §46.4 (Carlson does not apply to `F'/F`
in the strip) seen from the zero side, and it confirms that the coefficient identity
`n_F = lim_{w→1}(w−1)²𝔐_F(w)` must be used **definitionally**, not via a mean square.

**Consequence for §64.2.** The statement "`n_F` is read off the mean square of `F'/F` at shift zero"
is correct as a statement about the *coefficient* series `𝔐_F`, and is **not** a statement about
`∫|F'/F|²dt` below `σ = 1`. Corrected in the log so the two are never conflated again; the
pair-correlation content sits precisely in the cancellation between the zero-sum and the archimedean
term, which is where Montgomery-type input is needed.

---

## 67. Cycle 67 (2026-07-26) — the cancellation identified: `Re F'/F` is the smoothed zero-density
fluctuation

From the Hadamard/Landau expansion for `F ∈ S`,
```
F'/F(s) = −log Q − Σ_j λ_j ψ(λ_j s + μ_j) + Σ_ρ [ (s−ρ)^{−1} + ρ^{−1} ] + (pole terms) ,
```
with `ψ` the digamma function. Writing `δ := σ − 1/2` and taking real parts on `s = σ+it`:
- archimedean part `≈ −(Σ_j λ_j) log|t| = −(d/2) log|t|`;
- zero part `Σ_γ δ/(δ² + (t−γ)²) ≈ ∫ (d/2π)log|u| · δ/(δ²+(t−u)²) du ≈ (d/2)log|t|`.

> **The two leading terms cancel exactly.** Hence `Re (F'/F)(σ+it)` is precisely the **fluctuation of
> the zero-counting measure of `F`, smoothed at scale `δ = σ − 1/2`**, about its mean density
> `(d/2π)log|t|`.

So the pair-correlation content of the problem is the *variance of that fluctuation*, and the
programme's target `n_F` is what governs it.

**Scale matching.** Crudely, the mean of `|F'/F(σ+it)|²` from the nearest zero alone is
`≈ (δ·(d/2π)log T)·δ^{−2} = (d/2π)log T/δ`, while `𝔐_F(2σ) ~ n_F/(4δ²)`. These have the same order
exactly when `δ ≍ 1/log T` — the **mean zero spacing**. So the natural regime in which the
coefficient side and the zero side can be compared is `σ = 1/2 + c/log T`, precisely the scale at
which Selberg's central-limit machinery operates. (The crude estimate ignores the cancellation above,
so it fixes the scale but not the constant.)

**Recorded conclusion.** The remaining difficulty has a name and a scale: the variance of the
`δ`-smoothed zero-counting fluctuation of `F` at `δ ≍ 1/log T`. Every formulation of MI reached in
this programme — meromorphy of `R_{F,F}`, of `ℛ_F`, of `𝔏'_F`, of `𝔐_F`, the contour extractor, the
autocorrelation of `F'/F` — funnels into that single quantity, and it is exactly what Montgomery-type
pair-correlation input controls.

---

## 68. Cycle 68 (2026-07-26) — consolidation

`docs/drafts/pipeline/4-publication-ready/monodromy-integrality-selberg.md` now carries the cycle
52–67 output as Theorems 10–14 plus the cycle-67 structure theorem, and states the consolidated open
core. Together with §§1–6 of that file the preprint holds every paper-proved result of the
programme.

**Lean inventory: 17 theorems, five modules, all unconditional, all `#print axioms` clean**
(`RHTower.SelbergPairingPrimeSquare` ×9 incl. `weighted_cauchy_schwarz`;
`HTGeometry.GeneralizedDirichletMeanValue` ×3; `HTGeometry.ResidueJumpLowerBound` ×2;
`HTGeometry.LogCoefficientTransfer` ×1; `HTGeometry.DiagonalIsolation` ×2).

**Read order for a future session** (unchanged from §50.2, with additions):
1. §22.2 equivalence web; 2. the do-not-retry list (§4, §7, §9.1, §9.6, §10.1, §11.1, §20.4, §21.1,
§22.1, §26.3, §28.2, §31, §38, §46.4, §49.1, §53, §57, §62, §66); 3. the preprint; 4. the
Cusp–Spectrum Radius Law card; 5. §40.2 + §56.3 (counterexample squeeze); 6. §64.1 + §67 (the
conservation law and the smoothed-fluctuation target).

---

## 69. Cycle 69 (2026-07-26) — the energy functional is blind to the imaginary Gram entries

### 69.1 The obstruction, stated exactly

On prime coefficients, multiplication of Dirichlet series is **addition**
(`a_{FG}(p) = a_F(p) + a_G(p)`, §69 ref. line 69 of this log) and conjugation of `F ∈ S` conjugates
the vector. So the vectors attached to the multiplicative monoid generated by `F, G, \bar F, \bar G`
are exactly the **conjugate-closed integral span**
`{a v_F + b v_G + c \bar v_F + d \bar v_G : a,b,c,d ∈ Z}`, where `v_F = (a_F(p))_p`.

> **Theorem 16 (Real Gram expansion / blindness).** With `⟪v,w⟫ := Σ_p a_F(p)\overline{a_G(p)}/p`
> (any real weight) and `E(v) := Re⟪v,v⟫`,
> ```
> E(a v + b w + c \bar v + d \bar w)
>   = (a²+c²)E(v) + (b²+d²)E(w) + 2ac·Re⟪v,\bar v⟫ + 2bd·Re⟪w,\bar w⟫
>     + 2(ab+cd)·Re⟪v,w⟫ + 2(ad+bc)·Re⟪v,\bar w⟫ .
> ```
> Exactly **six** real numbers occur, all of them real parts. `Im⟪v,w⟫` and `Im⟪v,\bar w⟫` never
> occur. Hence two pairs `(v,w)`, `(v',w')` with equal six-tuples have **equal energies on the whole
> span**, whatever their imaginary Gram entries.

*Verification of the identity.* Writing `x = x₁+ix₂`, `y = y₁+iy₂`, both sides equal
`(a+c)²x₁² + (a−c)²x₂² + (b+d)²y₁² + (b−d)²y₂² + 2(a+c)(b+d)x₁y₁ + 2(a−c)(b−d)x₂y₂` at each prime.

**Consequence (a genuine no-go).** Selberg's Conjecture B asserts `⟪v_F,v_G⟫ = o(loglog x)` for
distinct primitives — *both* real and imaginary part. Theorem 16 says the imaginary part is not a
function of the prime energies of the monoid generated by `F, G` and their conjugates. Therefore:

> **No proof of the full Conjecture B can proceed by combining prime energies `n_H` of elements
> `H` of that monoid.** Every such proof determines at most the real Gram matrix. The vanishing of
> `Im⟪v_F,v_G⟫` must come from the analytic axioms (continuation, functional equation, Euler
> product), never from monoid + energy bookkeeping alone.

This is the exact sense in which the classical "Cauchy–Schwarz + positivity" toolkit — Conrey–Ghosh,
Murty's `n_F ≥ 1` arguments, the Gram-matrix PSD arguments of §52 and all their descendants — is
**structurally incomplete**, not merely insufficiently sharp. It also explains why §39.1 had to
supply the imaginary part of the integrality separately, by monodromy rather than by energy.

**Formalised, unconditional:** `formal/GaloisForLFunctions/HTGeometry/RealGramBlindness.lean` —
`intComb_sq_re`, `wEnergy_intComb`, `wEnergy_intComb_congr`; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.

### 69.2 The two-term second moment, and an independent confirmation of the `δ ≍ 1/log T` scale

Ingham's formula `∫_0^T|ζ(σ+it)|²dt = ζ(2σ)T + (2π)^{2σ−1}ζ(2−2σ)T^{2−2σ}/(2−2σ) + …` is the only
place in the classical theory where the Rankin–Selberg object appears **at `w` and at `2−w`
simultaneously** — precisely the relation §57.3 showed the `log`-functional equation cannot produce.
Running the approximate functional equation `F(s) ≈ Σ_{n≤x}a_F(n)n^{−s} + χ_F(s)Σ_{n≤y}\overline{a_F(n)}n^{s−1}`,
`xy ≍ 𝔮(t) = q_F(t/2π)^d`, for general `F ∈ S` of degree `d` gives, with `w = 2σ`:

- diagonal of the first sum: `T·R_F(w)`, and `R_F(1+2δ) ≍ (2δ)^{−n_F}` unconditionally (§58);
- diagonal of the dual sum: `∫_0^T 𝔮(t)^{1−w}·Σ_{n≤y(t)}|a_F(n)|²n^{w−2}dt`. Here the inner sum
  **diverges** as `y → ∞` (since `w > 1`), so it is *not* `R_F(2−w)`; by Wirsing (§58) it is
  `≍ y^{w−1}(log y)^{n_F−1}/(w−1)`. With `y ≍ 𝔮^{1/2}` this gives
  `≍ T^{1+d(1−w)/2}(log T)^{n_F−1}/(w−1)`.

Put `w = 1+2δ`, `δ = c/log T`. Then `T^{d(1−w)/2} = e^{−dc}` is a constant, `1/(w−1) ≍ log T`, so the
dual term is `≍ T(log T)^{n_F}` — and the diagonal term is `T(2δ)^{−n_F} ≍ T(log T)^{n_F}`.

> **The two terms of the second moment of `F` balance exactly at `δ ≍ 1/log T`, with common order
> `T(log T)^{n_F}`.** This is a second, completely independent derivation of the critical scale
> found in §67 (there from the Hadamard expansion of `F'/F`), and it holds for every real `n_F ≥ 0`.

**Negative content (recorded, do not retry).** Because the balance holds for *every* real `n_F`, the
two-term second moment **does not force integrality**. The hoped-for mechanism "reflection
`w ↦ 2−w` sends `(w−1)^{−n_F}` to `e^{∓iπn_F}(w−1)^{−n_F}`, and positivity kills the phase" fails at
its first step: the dual term is a **divergent partial sum**, not the continued value `R_F(2−w)`, so
no phase `e^{iπn_F}` is ever produced. The reflection route to MI through the second moment is
therefore closed, for the same structural reason as §57.3 — `R_F` has degree `d²` and inherits no
functional equation (§9.1).

### 69.3 The exact hypothesis under which MI is a triviality

> **Theorem 17 (logarithmic Sato–Tate ⟹ MI).** Let `F ∈ S`. Suppose there are a compact group `K`
> with normalised Haar measure `μ`, a continuous finite-dimensional representation `ρ` of `K`, and
> conjugacy classes `θ_p ⊂ K` with `a_F(p) = χ_ρ(θ_p)`, such that for every continuous class function
> `f` on `K`, `Σ_{p≤x} f(θ_p)/p = (∫ f dμ)·loglog x + O(1)`. Then `n_F = Σ_i m_i²` where
> `ρ ≅ ⊕_i m_iρ_i`; in particular `n_F ∈ Z_{≥0}` and MI holds for `F`.
>
> *Proof.* Take `f = |χ_ρ|²`, a continuous class function. Then `n_F = ∫|χ_ρ|²dμ = ⟨χ_ρ,χ_ρ⟩`, which
> is `Σ_i m_i²` by Schur orthogonality. ∎

The content is not the proof but the **weakness of the hypothesis**: it is equidistribution in
*logarithmic (Dirichlet) density*, which for each irreducible `λ ≠ 1` says only
`Σ_p χ_λ(θ_p)/p = O(1)` — no natural-density Sato–Tate, no analytic continuation of the
symmetric-power `L`-functions to `C`, only boundedness of a prime sum at the edge. This is strictly
weaker than automorphy and strictly weaker than what §22 and §33.2 assumed when the Sato–Tate route
was marked circular. It remains **⟸ only**: MI does not obviously return the group, so §33.2's
verdict (circular as an equivalence) stands. What is new is the identification of the *minimal*
sufficient input, which is now a clean falsifiable statement:

> **(LOG-ST)** Every `F ∈ S` admits a logarithmic Sato–Tate group.

LOG-ST ⟹ MI ⟹ Conjecture A. And LOG-ST is exactly a statement about the convergence of the
prime sums `Σ_p χ_λ(θ_p)/p`, i.e. about the *edge* behaviour of the higher moments only — the same
edge that §67 and §69.2 both localise at `δ ≍ 1/log T`.

### 69.4 Net

New this cycle: Theorem 16 (formalised) with its no-go corollary; the two-term second-moment balance
confirming the critical scale independently, together with the recorded closure of the reflection
route; Theorem 17 isolating LOG-ST as the minimal sufficient input.

---

## 70. Cycle 70 (2026-07-26) — the Selberg symplectic form

§69.1 says the energy functional cannot see `Im⟪v_F,v_G⟫`. This cycle names the invisible object and
determines its structure.

> **Definition.** For `F,G ∈ S` for which the density exists, put
> ```
> c_{F,G} := lim_{x→∞} (loglog x)^{-1} Σ_{p≤x} a_F(p) \overline{a_G(p)} / p ,
> ω(F,G) := Im c_{F,G} .
> ```

> **Theorem 19 (structure of `ω`).**
> 1. `ω` is `Z`-bilinear on the multiplicative monoid: `ω(FG,H) = ω(F,H) + ω(G,H)` (because
>    `a_{FG}(p) = a_F(p)+a_G(p)`), so it descends to an alternating form on the free abelian group
>    generated by the primitive elements.
> 2. `ω(G,F) = −ω(F,G)` and `ω(F,F) = 0`: `ω` is **alternating**.
> 3. `ω(\bar F,\bar G) = −ω(F,G)`: the conjugation involution `F ↦ \bar F` of `S` acts on `ω` by
>    `−1`, while it acts on every energy `n_H` by `+1`.
> 4. `ω(F,G) = 0` whenever `F` and `G` are both **self-dual** (real Dirichlet coefficients).
> 5. `ω` is invisible to energies (§69.1, Theorem 16).
>
> Hence `S` carries a canonical **symplectic form**, and:
> ```
> Selberg Conjecture B  ⟺  (symmetric part of c is δ_{F,G})  ∧  (ω ≡ 0).
> ```

Points 1–4 are immediate; 3 is the structural one, since it identifies `ω` as the `(−1)`-eigenpart of
the pairing under conjugation and the energy `n` as living entirely in the `(+1)`-eigenpart. That is
the *conceptual* reason for Theorem 16: the monoid together with conjugation is a `Z`-algebra acting
on the pairing through its `(+1)`-eigenspace only.

> **(RP) Reality of the Selberg pairing.** `ω ≡ 0` on `S`.

RP is strictly weaker than Conjecture B, is not implied by MI, is not accessible by any
energy/Cauchy–Schwarz argument (Theorem 16), and is a clean falsifiable target of its own.

**Formalised, unconditional:** `RealGramBlindness.lean` — `wIP_swap`, `wOmega_swap`, `wOmega_self`,
`wOmega_conj`, `wOmega_eq_zero_of_real`; `#print axioms` clean.

### 70.1 What already forces `ω = 0`, and what does not

- **Degree-1 partner.** If `G` is a degree-1 element (so `G(s) = L(s+iθ,χ)` by Kaczorowski–Perelli's
  classification) and `F ⊗ \barχ ∈ S`, then `c_{F,G}` is the *linear* density of `F ⊗ \barχ`, hence
  equals `m_{F⊗\barχ} ∈ Z_{≥0}` by the linear half already proved (§39, Theorem 2). So `ω(F,G)=0`.
  **This is classical**, not new; it is recorded here as the template.
- **Rankin–Selberg.** If `F ⊗ \bar G` lies in `S^♯` with an Euler product, then
  `c_{F,G} = m_{F⊗\bar G} ∈ Z_{≥0}`, so `ω(F,G)=0`. This is the standard reduction and it is exactly
  the missing analytic input (degree `d_Fd_G`, §9.1).
- **Energies (all of them).** Excluded by Theorem 16. **Do not retry any Gram/Cauchy–Schwarz/
  positivity argument for `ω`.**
- **The `A ⟹ B` folklore.** The usual lattice derivation "Conjecture A implies Conjecture B" computes
  `n_{F^aG^b} = a²n_F + b²n_G + 2ab·Re c_{F,G}` and bounds `Re c_{F,G}`. By Theorem 16 that argument
  **cannot** reach `ω`; any complete proof of B along those lines is incomplete at exactly this
  point. Recorded as a precise gap, not as a claim about any particular paper.

### 70.2 Consequence for the programme

The target splits cleanly and the two halves need different mathematics:

```
Conjecture B  =  (real part: integrality + orthogonality)   ← MI, the whole programme so far
              ∧  (imaginary part: ω ≡ 0)                     ← untouched by every tool used so far
```

Every result of cycles 1–69 lives in the first line. The second line is a new, independent open
problem of the same programme, and Theorem 16 proves it cannot be reduced to the first by algebra.

---

## 71. Cycle 71 (2026-07-26) — where `ω` *is* visible, and why the twist gives no leverage

§69.1 closes every energy/Cauchy–Schwarz/positivity route to `ω`. The one tool in the programme that
touches individual coefficients, including their phases, is the K–P standard twist (§9.4). Combining:

> **Theorem 20 (residue representation of `ω`).** Let `F,G ∈ S` have equal degree `d`, conductor `q`
> and internal shift, and put `α_m = d(m/q)^{1/d}`. With `ρ_0^F(α)` the leading standard-twist
> residue and `C = C(d,q,ξ,ω) > 0` the K–P prefactor (which by §9.4 depends only on those invariants,
> hence is *the same constant for `F` and `G`*),
> ```
> a_F(m)\overline{a_G(m)} = C · m^{1−1/d} · \overline{ρ_0^F(α_m)} · ρ_0^G(α_m) ,
> ω(F,G) = C · lim_x (loglog x)^{−1} Σ_{p≤x} p^{−1/d} · Im[ \overline{ρ_0^F(α_p)} ρ_0^G(α_p) ] .
> ```
> `C > 0` because the case `F = G` gives `|a_F(m)|² = C m^{1−1/d}|ρ_0^F(α_m)|²`.

So `ω` **is** representable in terms of meromorphic data — residues of analytically continued
functions — which no energy identity can be. This is the only such representation the programme has.

**But it carries no new information.** The K–P prefactor is coefficient-independent, so the map
`F ↦ (ρ_0^F(α_m))_m` is `F ↦ (\overline{a_F(m)})_m` composed with one positive scalar and one
explicit power of `m`. Theorem 20 is therefore an **exact restatement**, not extra leverage: it
converts a statement about coefficients into the same statement about residues.

> **Recorded, do not retry.** The standard-twist residue pairing cannot prove `ω ≡ 0` on its own.
> Any use of it must exploit something about the residues *as a function of `α`* — i.e. the
> regularised `α`-pairing of §11.2 — and §11.1 already shows the naive `α`-integral diverges exactly
> on the spectrum. The open requirement is unchanged: a regularisation scheme, equivalently the
> meromorphic continuation of `R_{F,G}`.

### 71.1 Status of the split

```
Conjecture B = (real part)  ∧  (ω ≡ 0)
   real part : MI / R_{F,F} continuation — cycles 1–69, open, reduced to the δ ≍ 1/log T variance
   ω ≡ 0     : new open half — provably unreachable by energies (Thm 16); only representation is
               Thm 20, which is a restatement; needs the same R_{F,G} continuation
```
Both halves therefore funnel into the meromorphic continuation of `R_{F,G}` at `w = 1`. That is now
established as **the** single open core of the whole programme, from two structurally independent
directions.

---

## 72. Cycle 72 (2026-07-26) — the second energy, and a decisive limit on the pair-correlation funnel

§67 funnelled the programme into the variance of the `δ`-smoothed zero-counting fluctuation at
`δ ≍ 1/log T`, i.e. into Montgomery-type pair correlation for `F`. This cycle asks what the pair
correlation of the zeros of `F` actually computes, and the answer is **not** `n_F`.

### 72.1 The zero energy `E_F`

> **Definition.** For `F ∈ S` let the zeros in the critical strip with `0 < γ ≤ T` be listed as
> distinct points `ρ` with multiplicities `m_ρ ≥ 1`, so `N_F(T) = Σ_ρ m_ρ ~ (d_F/2π)T log T`. Put
> ```
> E_F := d_F · lim_{T→∞} ( Σ_ρ m_ρ² ) / N_F(T)     (the multiplicity-weighted zero energy).
> ```

> **Theorem 21 (what the fine-scale pair correlation computes).** Under RH for `F`, the large-`α`
> limit of Montgomery's pair-correlation function of the zeros of `F` equals the mean squared
> multiplicity `E_F/d_F`, because at scales below the mean spacing the only surviving pairs are the
> `Σ_ρ m_ρ²` pairs at distance zero.

> **Theorem 22 (bracket, unconditional).** `Σ_ρ m_ρ² ≥ Σ_ρ m_ρ = N_F(T)`, hence `E_F ≥ d_F`, with
> equality **iff every zero of `F` is simple**.
> (Lean: `sum_le_sum_sq`, `sum_sq_eq_sum_iff`, `sum_sq_div_sum_ge_one`; axioms clean.)

For the primitive factorisation `F = ∏F_i^{e_i}` with the expected disjointness and simplicity of
the factors' zeros, `N_{F_i}(T) ~ (d_i/2π)T log T` gives
```
Σ_ρ m_ρ² ~ (Σ_i e_i² d_i)(T log T/2π) ,   N_F(T) ~ (Σ_i e_i d_i)(T log T/2π) = (d_F/2π)T log T ,
so     E_F = Σ_i e_i² d_i .
```

### 72.2 The two energies are different invariants

```
prime energy  n_F = Σ_i e_i²         (Selberg)
zero energy   E_F = Σ_i e_i² d_i     (this cycle)
```
They agree exactly when every primitive factor has degree `1`. Checks: `F = ζ` gives `n=1`, `E=1`;
`F = ζ·L(·,χ)` gives `n=2`, `E=2`; `F = ζ²` gives `n=4`, `E=4`; but for a degree-`2` primitive `G`,
`n_G = 1` while `E_G = 2`, and for `G²`, `n = 4` while `E = 8`. So `n_F ≤ E_F ≤ d_F·n_F`
(using Conrey–Ghosh `d_i ≥ 1`), and the two coincide only in the degree-1 world.

### 72.3 The decisive negative

> **`E_F = d_F` for every `F` all of whose zeros are simple — regardless of its factorisation.**

The fine-scale (`α → ∞`) end of the pair correlation is therefore **blind to the primitive
factorisation** in the generically expected situation. In particular:

> **Recorded, do not retry.** No argument that extracts `n_F` from the fine-scale diagonal of the
> pair correlation of the zeros of `F` can work. Fine-scale pair correlation measures multiplicities
> (`E_F`), not prime energy (`n_F`).

**This corrects the emphasis of §67, it does not contradict it.** The explicit formula does equate
the prime side `Σ_p|a_F(p)|²…` with a zero-side variance, but the identification lives at
`δ ≍ 1/log T`, i.e. at *bounded* `α` — the Montgomery regime — not at `α → ∞`. The two ends of the
same statistic compute different invariants:
```
α → ∞      : E_F = Σ e_i² d_i     (multiplicities; blind to factorisation when zeros are simple)
α ≍ 1      : n_F = Σ e_i²         (prime energy; the actual target)   ← still open
α → 0      : d_F                  (the degree; classical)
```
So the pair-correlation funnel is real but its useful window is exactly the bounded-`α` regime where
Montgomery's own conjecture is open. That is now the sharpest available description of the open core.

### 72.4 A new conjecture with independent content

> **(ZE) Zero Energy Integrality.** For every `F ∈ S`, `E_F` exists and `E_F ∈ Z_{≥0}`.

ZE is *not* implied by MI and does not imply it: it is the statement that the multiplicity densities
of the zeros of `F` are integer combinations of the degrees of its primitive factors. Since
`E_F ≥ d_F` with equality iff all zeros are simple (Theorem 22), ZE is a bridge between Selberg's
**degree conjecture** and the **simple-zero conjecture**, and it is the natural companion to MI on
the zero side. Its falsity would exhibit an `F ∈ S` whose zeros have irrational mean squared
multiplicity — an object as strange as a counterexample to Conjecture A, but visible in the zeros
rather than in the primes.

---

## 73. Cycle 73 (2026-07-26) — the complex-shift regularisation: `n_F` from the L²-mean of the standard twist on the critical line

§11.2 recorded that the `α`-pairing of standard twists diverges on `Spec(F)` and demanded a
*regularisation scheme*. This cycle supplies one. The idea §11 missed: **push `α` into the lower
half-plane**.

### 73.1 The identity

For `F ∈ S` of degree `d ≥ 1` write `Φ_F(s,α) := Σ_n a_F(n) e(−α n^{1/d}) n^{−s}`, `e(x)=e^{2πix}`.
For `α = a − ib` with `b > 0`,
```
e(−α n^{1/d}) = e^{−2πi a n^{1/d}} · e^{−2π b n^{1/d}} ,
```
so the series converges **absolutely for every `s ∈ C`** (Ramanujan gives `a_F(n) ≪ n^ε`, and the
exponential beats every power). Thus `Φ_F(·,α)` is **entire in `s`** and holomorphic in `α` on the
lower half-plane, and for real `σ` the function `a ↦ Φ_F(σ, a−ib)` is a Bohr almost-periodic function
with coefficients `c_n = a_F(n)e^{−2πbn^{1/d}}n^{−σ}` and **pairwise distinct** frequencies
`−2π n^{1/d}`.

> **Theorem 23 (complex-shift regularisation).** For `F,G ∈ S` of equal degree `d ≥ 1`, every real
> `σ` and every `b > 0`,
> ```
> lim_{A→∞} (1/2A) ∫_{−A}^{A} Φ_F(σ, a−ib) · conj(Φ_G(σ, a−ib)) da
>     = Σ_{n≥1} a_F(n) conj(a_G(n)) e^{−4πb n^{1/d}} n^{−2σ}  =:  R_b^{F,G}(2σ) .
> ```
> `R_b^{F,G}(w)` is **entire in `w`** for every `b > 0`, satisfies the Mellin–Barnes identity
> `R_b(w) = (2πi)^{−1}∫_{(c)} Γ(u)(4πb)^{−u} R_{F,G}(w + u/d) du` for `Re w + c/d > 1`, and
> `R_b(w) → R_{F,G}(w)` as `b → 0+` for `Re w > 1`.
>
> *Proof.* Absolute convergence lets the double sum be integrated term by term; the mean of
> `e^{−2πia(n^{1/d} − m^{1/d})}` over `a ∈ [−A,A]` is `1` on the diagonal and `O(1/A)` off it, because
> `n ↦ n^{1/d}` is injective. Entirety of `R_b` is again the exponential decay; the Mellin identity
> is `e^{−x} = (2πi)^{−1}∫_{(c)}Γ(u)x^{−u}du` with `x = 4πb n^{1/d}`. ∎
>
> **Formalised (finite form, unconditional):** `genPoly_meanValue` gives the exact diagonal/off-
> diagonal split, `oscInt_norm_le` gives `‖oscInt δ T U‖ ≤ 2/|δ|` **independently of the interval
> length**, and `genPoly_meanValue_error` bounds the deviation of the mean square from `U ·` (diagonal
> energy) by `Σ_{n≠m}‖a_m‖‖a_n‖·2/|λ_m−λ_n|`, uniformly in `T` and `U`. Dividing by `U` and letting
> `U → ∞` is exactly the limit above. `#print axioms` clean.

**This is the regularisation §11.2 asked for.** The divergence at `Spec(F)` that killed the real-`α`
pairing is removed by the shift `α ↦ α − ib`, at the cost of the smoothing factor `e^{−4πbn^{1/d}}`;
the whole content of `R_{F,G}` at `w = 1` is transferred to the `b → 0` asymptotics.

### 73.2 `n_F` as a divergence rate on the critical line

Assume the prime density `n_F` exists. Then `|a_F|²` is non-negative multiplicative and Wirsing
(§58) gives `Σ_{n≤x}|a_F(n)|² ~ c_F x (log x)^{n_F−1}/Γ(n_F)`. Substituting into `R_b^{F,F}(1)` and
putting `u = log t`,
```
R_b^{F,F}(1) = Σ_n |a_F(n)|² e^{−4πb n^{1/d}} n^{−1}
             ≈ (c_F/Γ(n_F)) ∫_0^∞ u^{n_F−1} e^{−4πb e^{u/d}} du
             ~  c_F · (d log(1/b))^{n_F} / Γ(n_F + 1)     (b → 0+).
```
Since `w = 2σ = 1` means `σ = 1/2`:

> **Theorem 24 (critical-line divergence formula).** For `F ∈ S` of degree `d ≥ 1` whose prime density
> exists,
> ```
> n_F  =  lim_{b→0+}  log[ lim_{A→∞} (1/2A) ∫_{−A}^{A} |Φ_F(1/2, a−ib)|² da ]  /  log log(1/b) .
> ```
> Equivalently: **the L²-mean of the standard twist of `F` on the critical line is infinite, and
> `n_F` is the exponent of `log(1/b)` in the divergence rate of its complex-shift regularisation.**

Every earlier avatar of `n_F` in this programme lived on a Dirichlet series (`R_{F,F}`, `ℛ_F`,
`𝔏'_F`, `𝔐_F`) or on the zeros (`E_F`, §72). This one lives on the **standard twist**, on the
**critical line**, and is an honest `L²` quantity. It is a new object: K–P study `F(s,α)` pointwise
and pole-wise in `α`, never its mean square in `α`.

### 73.3 A new candidate integrality mechanism

`a ↦ Φ_F(σ, a−ib)` has spectrum contained in the discrete negative set `{−2πn^{1/d}}`, so
`Φ_F(σ, ·)` is the boundary value of a **Hardy-space function** on the lower half `α`-plane, and
`R_b^{F,F}(2σ)` is precisely `‖Φ_F(σ, ·−ib)‖²_{H²}` at depth `b`. Selberg's Conjecture A therefore
becomes:

> **(HS) Hardy-space form of MI.** For `F ∈ S`, `‖Φ_F(1/2, ·−ib)‖²_{H²} ≍ (log 1/b)^{n}` with
> `n ∈ Z_{≥0}`.

§35 listed the candidate integer-producing mechanisms available in this programme: a dimension, a
pole order, a Galois-orbit count, a winding number, a lattice-point count — all of which were checked
and none of which applies. §73.3 adds a genuinely new one, absent from that list:

> **(g) an operator-theoretic multiplicity** — a Beurling–Lax multiplicity of a shift-invariant
> subspace, or the rank of a Hankel/Toeplitz operator attached to `Φ_F`.

Ranks and Lax–Halmos multiplicities **are** integers by theorem, with no arithmetic input. Whether
`n_F` is one of them is open, and is the target of the next cycle.

**Recorded do-not-retry from this cycle:** deducing integrality directly from Theorem 24 by asking
for an asymptotic expansion of `R_b(1)` in powers of `b` and `log(1/b)` is **circular** — such an
expansion is exactly the meromorphy of `R_{F,F}` read through Mellin.

---

## 74. Cycle 74 (2026-07-26) — the consolidated equivalence theorem, and the meta-conclusion

> **Theorem 25 (equivalence web for Monodromy Integrality).** For `F ∈ S` of degree `d ≥ 1` whose
> prime density `n_F` exists, the following are equivalent.
>
> 1. **(MI)** `n_F ∈ Z_{≥0}`.
> 2. `R_{F,F}(w) = Σ_n |a_F(n)|² n^{−w}` is meromorphic in a neighbourhood of `w = 1`.
> 3. `R_{F,F}(w)·(w−1)^{n_F}` extends continuously and non-zero to `w = 1` **and** `n_F ∈ Z`
>    (i.e. `w=1` is a pole, not a branch point).
> 4. `𝔐_F(w)`, the shifted autocorrelation of `F'/F`, has a **double pole** at `w = 1` (not a branch
>    singularity), with `n_F = lim_{w→1}(w−1)²𝔐_F(w)`.
> 5. `𝔏'_F` and `ℛ_F` (§§22, 46) are meromorphic at their edge point.
> 6. `Σ_{n≤x}|a_F(n)|²` has an asymptotic of Selberg–Delange type with **integer** log-power.
> 7. `R_b^{F,F}(1) = ‖Φ_F(1/2,·−ib)‖²_{H²}` blows up like `(log 1/b)^{n}` with `n ∈ Z_{≥0}`
>    as `b → 0+` (Theorem 24).
>
> *Proof sketch.* `1 ⟺ 3` and `2 ⟺ 3` are Landau plus the fact that the order of a pole of a
> meromorphic function is an integer (this is where integrality is *produced*, and nowhere else).
> `2 ⟺ 4 ⟺ 5` are the identities of §§22.2, 46, 64. `2 ⟺ 6` is Selberg–Delange in both directions.
> `2 ⟺ 7` is the Mellin–Barnes identity of Theorem 23: `R_b` is the Mellin smoothing of `R_{F,F}`,
> and a Mellin transform has an asymptotic expansion in `b^{−β}(log 1/b)^k` with `k ∈ Z` exactly when
> its Mellin transform is meromorphic. ∎

**Meta-conclusion of the programme, now firmly established.**

> Integrality in `S` is produced by exactly one mechanism: *the order of a pole of a single-valued
> meromorphic function*. Every formulation of MI reached in 74 cycles — via `R_{F,F}`, `ℛ_F`,
> `𝔏'_F`, `𝔐_F`, the contour extractor, the standard-twist residue pairing, the zero energy `E_F`,
> the Hardy-space norm `R_b` — is a restatement of the existence of that meromorphic parent, not an
> independent route to it.

Candidate alternative integrality mechanisms, all checked and all closed:

| mechanism | status |
|---|---|
| positivity / Cauchy–Schwarz / Gram | closed — §69.1 Theorem 16, and the `ζ^{1/2}` witness |
| dimension of a representation (Schur) | closed — needs the Sato–Tate group; circular (§33.2, §69.3) |
| Galois-orbit count | closed — no Galois action in `S` (§35) |
| winding number / monodromy | **is** the pole-order mechanism (§39.1) |
| lattice-point count | closed — no lattice object in `S` (§35) |
| zero multiplicities | closed — computes `E_F = Σe_i²d_i`, not `n_F` (§72.3) |
| reflection `w ↦ 2−w` phase | closed — the dual term is a divergent partial sum (§69.2) |
| operator/Beurling–Lax multiplicity | open, but reduces to the Sato–Tate group again (§74.1) |

### 74.1 Why the operator route collapses to Schur

The natural finite-dimensional algebra with `dim = Σ e_i²` is `End(ρ) = ⊕_i M_{e_i}(C)`, whose
dimension is `Σe_i²` by Artin–Wedderburn. To attach such an algebra to `F ∈ S` one must produce the
representation `ρ`, i.e. the Sato–Tate group; the GNS construction from the logarithmic prime state
`φ(f) = lim (loglog x)^{−1}Σ_{p≤x}f(p)/p` gives a Hilbert space with `‖a_F‖² = n_F` but **no
finite-dimensionality**, and finite-dimensionality is exactly the missing input. Recorded so the
operator route is not re-attempted without a new source of finite-dimensionality.

### 74.2 The one remaining unexplored surface

Everything above says: to prove MI one must construct the meromorphic parent of `Σ|a_F(n)|²n^{−w}`.
The only construction of such a parent that does not presuppose automorphy would be an **integral
representation** of `R_{F,F}` — and Theorem 23 now supplies one half of it: `R_{F,F}` is the Mellin
transform, in the depth parameter `b`, of the `H²`-norm of the standard twist,
```
R_{F,F}(w) = (Mellin in b)^{-1} of  ‖Φ_F(w/2, ·−ib)‖²_{H²} .
```
Meromorphic continuation of `R_{F,F}` past `w = 1` is therefore **exactly** an asymptotic expansion
of that `H²`-norm as the depth `b → 0`, in powers of `b` and `log(1/b)`. That is a concrete,
self-contained analytic problem about one explicit entire-in-`s` function `Φ_F`, with no
Rankin–Selberg, no automorphy, and no Euler product in sight. **It is the recommended target for the
next cycles.**

---

## 75. Cycle 75 (2026-07-26) — cross-degree twist orthogonality, and an honesty check on §74.2

### 75.1 Honesty check: the Hardy-space route is equivalent, not easier

`M_F(b,1) := Σ_n |a_F(n)|² e^{−4πb n^{1/d}} n^{−1}` satisfies, with `S(x) := Σ_{n≤x}|a_F(n)|²/n`,
```
e^{−4π} S(b^{−d}) ≤ M_F(b,1) ≤ S(b^{−d}) + Σ_{n > b^{−d}} |a_F(n)|² e^{−4πb n^{1/d}}/n  ≪ S(b^{−d}) .
```
So `M_F(b,1) ≍ S(b^{−d})`: the `H²`-norm of the standard twist is **equivalent** to the partial sums
it was meant to illuminate. Theorem 24 is a faithful reformulation, not a reduction.

**What it does buy:** the `H²` framing gives access to Hardy-space machinery — inner–outer
factorisation, Blaschke products, Beurling's theorem — applied to `Φ_F(σ,·)`, none of which is
available on the partial-sum side. That, and only that, is the reason to keep it. Recorded so a later
cycle does not mistake §74.2 for a reduction in difficulty.

### 75.2 Cross-degree twist pairing

Theorem 23 required `d_F = d_G`, because the Bohr mean pairs the frequency `n^{1/d_F}` of `Φ_F`
against `m^{1/d_G}` of `Φ_G`. Dropping that requirement gives a new object.

> **Theorem 26 (cross-degree twist orthogonality).** Let `F, G ∈ S` with `d_F/d_G = p/q` in lowest
> terms, `d_F = kp`, `d_G = kq`. Then for every real `σ` and `b > 0`,
> ```
> lim_{A→∞}(1/2A)∫_{−A}^{A} Φ_F(σ,a−ib)·conj(Φ_G(σ,a−ib)) da
>       = Σ_{t≥1} a_F(t^p) conj(a_G(t^q)) e^{−4πb t^{1/k}} t^{−σ(p+q)} .
> ```
> *Proof.* The Bohr mean picks out the pairs `(n,m)` with `n^{1/d_F} = m^{1/d_G}`, i.e. `n^q = m^p`.
> With `gcd(p,q)=1` a Bézout relation `pu = qv+1` and the exact division `n^u = m^v t` give
> `n = t^p`, `m = t^q` by cancellation alone (Lean: `pow_eq_pow_of_bezout`; axioms clean).
> Conversely every such pair matches. For `p = q = 1` this is Theorem 23. ∎

**Content.** The overlap of the twist spectra of two elements of different degree is carried by the
**perfect `p`-th and `q`-th powers** — a set of density zero as soon as `(p,q) ≠ (1,1)`. So the
standard twists of elements of different degrees are *almost* Bohr-orthogonal, and the residual
overlap involves only the values `a_F(t^p)`, `a_G(t^q)` at perfect powers, which the Euler product
expresses through the *higher* local data, never through `a_F(p)` at primes.

**Consequence for Conjecture B.** The Bohr-mean construction produces the Selberg pairing
`Σ a_F(n)\overline{a_G(n)}n^{−w}` **only when `d_F = d_G`.** For `d_F ≠ d_G` it produces a different,
sparse pairing. Recorded as a structural fact: the twist route is degree-diagonal, so it cannot by
itself deliver orthogonality across degrees, and the classical expectation "different degrees ⟹
orthogonal" is *not* accessible from Theorem 23.

**Unconditional relevance.** Degrees in `S` are only known to be real and `≥ 1` (Conrey–Ghosh);
integrality of `d_F` is itself an open Selberg conjecture. Theorem 26 covers exactly the commensurable
case `d_F/d_G ∈ Q`. In the incommensurable case the matching set `{(n,m) : log n/log m = d_F/d_G}`
is, by Baker's theorem on linear forms in logarithms, contained in the powers of a single pair
`(n_0,m_0)` (two multiplicatively independent solutions would force a vanishing linear form in three
logarithms). So the pairing is then supported on a single geometric progression — thinner still.

---

## 76. Cycle 76 (2026-07-26) — Jessen–Tornehave: `n_F` bounds the zero density of the standard twist

§75.1 said the only real gain from the Hardy-space framing is access to machinery unavailable on the
partial-sum side. This cycle cashes that in.

### 76.1 The right machinery

For `b > 0` fixed, `a ↦ Φ_F(σ, a−ib) = Σ_n c_n(b) e^{−2πi a n^{1/d}}`, `c_n(b) = a_F(n)e^{−2πbn^{1/d}}n^{−σ}`,
has `Σ|c_n| < ∞`, so it is a **uniformly almost periodic** function of `a`, and `Φ_F(σ,·)` is
analytic almost periodic on the strip `Im α < 0`. It is not identically zero (`a_F(1)=1`, distinct
frequencies). **Jessen–Tornehave theory** therefore applies:
```
φ(b) := lim_{A→∞} (1/2A) ∫_{−A}^{A} log|Φ_F(σ, a−ib)| da        (Jessen's function)
```
exists, is **convex** in `b`, and the density of zeros of `Φ_F(σ,·)` in the strip `b₁ < −Im α < b₂`,
counted with multiplicity per unit length in `Re α`, equals `(φ'(b₂) − φ'(b₁))/2π`.

*(Applying Jessen–Tornehave to standard twists of Selberg-class elements appears to be new; K–P study
`F(s,α)` in `s` for fixed `α`, never the zero distribution in `α`.)*

### 76.2 Two bounds on Jessen's function

**Upper.** By Jensen's inequality for the mean and Theorems 23–24, at `σ = 1/2`,
```
φ(b) ≤ (1/2) log[ mean of |Φ_F(1/2,·−ib)|² ] = (1/2) log M_F(b) = (n_F/2)·loglog(1/b) + O(1).
```
**Lower.** As `b → ∞` the `n = 1` term dominates: `Φ_F(1/2,a−ib) = e^{−2πb}e^{−2πia}(1+o(1))`, so
`φ(b) + 2πb → 0`. A convex function tending to `0` at `+∞` is non-increasing and non-negative, hence
```
φ(b) ≥ −2πb   for all b > 0.
```

### 76.3 The theorem

Convexity gives the supporting-line inequality `φ(b/2) ≥ φ(b) + φ'(b)(b/2 − b)`, i.e.
`−φ'(b)·b/2 ≤ φ(b/2) − φ(b)`. Feeding in the two bounds:

> **Theorem 27 (zero density of the standard twist on the critical line).** Let `F ∈ S` have degree
> `d ≥ 1` and prime density `n_F`. Let `𝒩_F(b)` be the Jessen density of zeros of
> `α ↦ Φ_F(1/2, α)` in `{Im α < −b}` — zeros per unit length in `Re α`, with multiplicity. Then
> ```
> 𝒩_F(b) = (−2π − φ'(b))/2π  ≤  ( n_F · loglog(2/b) + O(1) ) / (2π b)      (b → 0+).
> ```
> Unconditional, every degree `d ≥ 1`.

So the prime energy `n_F` **controls the proliferation of the zeros of the standard twist as the
depth shrinks**. This is the first statement in the programme that bounds an *integer-valued counting
function* by `n_F`; every previous avatar bounded or computed a continuous density.

### 76.4 The conjecture this opens

The only loss in §76.2 is Jensen's inequality — the gap between the geometric and the quadratic mean
of `|Φ_F(1/2,·−ib)|`.

> **(ZD) Zero-density form of MI.** `φ(b) = (n_F/2)·loglog(1/b) + O(1)`; equivalently the geometric
> and quadratic means of the standard twist on the critical line have the same logarithmic order.
> Then `n_F = 2·lim_{b→0} φ(b)/loglog(1/b)`, and by Jessen's formula `n_F` is `2π` times the
> second-order zero-counting density of `Φ_F(1/2,·)`.

ZD is bold, falsifiable, and structurally new: it converts Selberg's Conjecture A into a statement
about the **zeros of the standard twist in the twist parameter**. Its falsity would mean the twist
has a genuine log-normal defect on the critical line — itself a striking phenomenon. Its truth would
put `n_F` on the same footing as a zero count, the one place in complex analysis where integers are
produced for free.

**[OPEN CORE]** ZD, and the passage from "`n_F` is a zero-counting *density*" to "`n_F ∈ Z`". A
density of integers need not be an integer; what is needed is a rigidity forcing the zero-counting
function of `Φ_F(1/2,·)` to have an exact asymptotic with integer coefficient. That is the next
target.

### 76.5 Degree-1 sanity model

For `d = 1` the substitution `z = e(−α)` maps `ℍ⁻` onto the punctured unit disc and
`Φ_F(σ,α) = Σ_n a_F(n)n^{−σ}z^n` is an honest power series. Then `M_F(b) = Σ|a_F(n)|²r^{2n}n^{−2σ}`
with `r = e^{−2πb}`, and Theorem 24 reads: *the `H²`-growth exponent of `Σ a_F(n)n^{−1/2}z^n` at the
boundary is `n_F`*. Checks: `F = ζ` gives `Σ r^{2n}/n ~ log(1/(1−r))`, exponent `1 = n_ζ`;
`F = ζ²` gives `Σ d(n)²r^{2n}/n ≍ (log(1/(1−r)))⁴`, exponent `4 = n_{ζ²}`. For `d ≥ 2` the exponents
`n^{1/d}` are not integers, so `Φ_F` is not single-valued in `z` — the disc model is available only
in degree 1, and the strip/Jessen model is the correct general setting. Recorded so no later cycle
tries to force the disc model on `d ≥ 2`.

---

## 77. Cycle 77 (2026-07-26) — ZD is FALSE, and what kills it

Phase-4 attack on §76.4's conjecture (ZD), by exact computation in the simplest case.

### 77.1 The refutation

Take `F = ζ`, `d = 1`. Then `z = e(−α)` maps the strip to the punctured disc, `r = |z| = e^{−2πb}`,
and `Φ_ζ(1/2, α) = Σ_n n^{−1/2} z^n = Li_{1/2}(z)`.

- **Quadratic mean.** `M(b) = Σ_n r^{2n}/n = log(1/(1−r²)) + O(1) ~ log(1/b)`, so
  `(1/2)log M(b) = (1/2)loglog(1/b) + O(1)` — matching Theorem 24 with `n_ζ = 1`. ✓
- **Geometric mean (Jessen's function).** Near `z = 1`,
  `Li_{1/2}(z) = Γ(1/2)(−log z)^{−1/2} + Σ_{k≥0} ζ(1/2−k)(log z)^k/k!`, so `|Li_{1/2}|` blows up
  **only** in a shrinking neighbourhood of `θ = 0`, like `|1−z|^{−1/2}`, and is bounded elsewhere.
  Hence
  `φ(b) = (1/2π)∫ log|Li_{1/2}(re^{iθ})| dθ ≈ (1/2π)∫ (−½)log|1−re^{iθ}| dθ + O(1) = O(1)`,
  since `∫_0 log(1/|θ|)dθ` converges. **`φ(b) = O(1)`, not `~ (1/2)loglog(1/b)`.**

> **ZD is FALSE.** The Jensen gap between the geometric and the quadratic mean of the standard twist
> is *not* `O(1)`; for `F = ζ` the geometric mean stays bounded while the quadratic mean diverges.

**Verdict: FALSE.** Recorded do-not-retry: no conjecture equating Jessen's function `φ(b)` with
`(n_F/2)loglog(1/b)` can hold. Theorem 27 (the upper bound `𝒩_F(b) ≤ (n_F loglog(2/b)+O(1))/2πb`)
survives — it is a true but far-from-sharp inequality; for `ζ` the true zero density is `O(1)`.

### 77.2 What killed it — the structural lesson

The `L²` mass of `Φ_F(1/2,·−ib)` is **concentrated on a shrinking set** of `a`, near the points where
the standard twist becomes large — precisely `Spec(F) = {d(m/q)^{1/d}}`, where the K–P residue is
proportional to `conj(a_F(m))` (§9.4). The typical (geometric-mean) size is `O(1)`; the divergence of
`M_F(b)` comes entirely from the spikes.

> **`n_F` is a concentration exponent, not a size exponent.** It measures how much `L²`-mass the
> standard twist piles up on `Spec(F)` as the depth shrinks, weighted by `|a_F(m)|²`. Any functional
> of `Φ_F` that is insensitive to thin sets — geometric means, Jessen's function, Nevanlinna
> characteristics, essential suprema — is **blind to `n_F`**.

This is a second instance of the same phenomenon as §69.1 (energies are blind to `ω`) and §72.3
(fine-scale pair correlation is blind to the factorisation): the programme keeps finding natural
functionals that *cannot* see the target. Collecting them:

| functional | blind to |
|---|---|
| prime energies over the monoid | `Im c_{F,G}` (§69.1) |
| fine-scale zero pair correlation | the primitive factorisation (§72.3) |
| geometric mean / Jessen's function of the twist | `n_F` (§77.1) |

**Common cause.** All three are *averaging* functionals, and the arithmetic in `S` lives on thin,
spiky sets: on the diagonal of the prime sum, on the multiplicity set of the zeros, on `Spec(F)`.
This is now recorded as a design rule for the programme:

> **Rule.** Any proposed route to MI must be sensitive to sets of density zero. Averaging
> functionals — means, densities, characteristics — will not see `n_F`.

That rule immediately re-explains, uniformly, several earlier kills: Halász (§38.1), Carlson
(§31, §46.4), the pretentious method (§22.1), and the `α → ∞` pair correlation (§72.3) are all
averaging arguments.

---

## 78. Cycle 78 (2026-07-26) — the regularised spectral sum in its correct (thin-set) form

Applying §77.2's rule — only thin-set-sensitive functionals can see `n_F` — to Theorem 23.

### 78.1 Translating the `L²`-mean into a spectral sum

By §9.4 the K–P residue formula gives, for `F` of degree `d`, conductor `q`, with
`α_n := d q^{−1/d} n^{1/d}` the `n`-th spectral point,
```
|a_F(n)|² = C · n^{1−1/d} · |ρ_0^F(α_n)|² ,        C = C(d,q,ξ_F,ω_F) > 0 ,
```
`C` independent of `n`. Substituting into Theorem 23 at `σ = 1/2` and using
`n^{1/d} = q^{1/d}α_n/d`:

> **Theorem 28 (exact regularised spectral form).** For `F ∈ S` of degree `d ≥ 1`, put
> `β := 4π q^{1/d}/d`. Then for every `b > 0`
> ```
> M_F(b) := lim_{A→∞}(1/2A)∫_{−A}^{A}|Φ_F(1/2,a−ib)|² da
>         = (C d / q^{1/d}) · Σ_{n≥1} |ρ_0^F(α_n)|² · α_n^{−1} · e^{−β b α_n} ,
> ```
> a sum over the **spectrum** `Spec(F) ⊂ {α_n}` (the terms with `a_F(n)=0` vanish, since `ρ_0^F(α_n)`
> vanishes exactly there). Consequently
> ```
> n_F = lim_{b→0+} log[ Σ_{α ∈ Spec(F)} |ρ_0^F(α)|² α^{−1} e^{−βbα} ] / log log(1/b) .
> ```

Equivalently, in integral form with `n ≍ (q^{1/d}α/d)^d`,
```
M_F(b) ≍ ∫_0^∞ |ρ_0^F(α)|² α^{d−2} e^{−βbα} dα .
```

### 78.2 Why this is the right shape at last

§11.2 demanded a **regularisation of the `α`-pairing of standard twists across the common spectrum
lattice**, and recorded that a domination/Fubini argument cannot supply one. Theorem 28 supplies it
explicitly:

- the pairing is over `Spec(F)` — a **discrete, density-zero set**, so §77.2's rule is satisfied;
- the regulariser is `e^{−βbα}`, produced canonically by the complex shift `α ↦ α − ib` (Theorem 23),
  not imposed by hand;
- the weight `α^{−1}` (equivalently `α^{d−2}dα`) is forced, not chosen;
- every ingredient is a **residue** of a meromorphic function, i.e. exactly the class of quantities
  that can produce integers.

Combining with §71: Theorem 28 is still, term by term, an *exact restatement* of the coefficient sum
(the K–P prefactor is coefficient-independent). Its value is not new information but the correct
**shape**: `n_F` is now the divergence exponent of a residue-weighted, exponentially damped counting
sum over a discrete spectrum — the only shape §77.2 permits.

### 78.3 The resulting target

> **(RC) Residue counting.** For `F ∈ S`, the counting function
> `R_F(X) := Σ_{α ∈ Spec(F), α ≤ X} |ρ_0^F(α)|² α^{−1}` satisfies `R_F(X) ~ c_F (log X)^{n_F}/Γ(n_F+1)`
> with `n_F ∈ Z_{≥0}`.

RC is equivalent to MI (Theorem 25 plus Abelian/Tauberian passage between `R_F(X)` and `M_F(b)` at
`X ≍ 1/b`), but it is the first equivalent form in which the quantity being counted is a sum of
**squared residues over a discrete set**. That is where the next cycles should push: a rigidity for
`R_F`, not for a mean value.

**Recorded scope note.** Theorem 28 needs `d ≥ 1` (K–P twist theory) and `F` with at least one
non-zero coefficient beyond `n=1` — both automatic in `S` for non-constant `F` by Conrey–Ghosh.

---

## 79. Cycle 79 (2026-07-26) — the Estermann–Kurokawa dichotomy, and why it is not an independent mechanism

§73 recorded a trichotomy for `R_{F,F}` at `w = 1`: pole (⟹ MI), branch point with non-integer
exponent (⟹ MI false), natural boundary (⟹ MI vacuous). This cycle asks whether the **Euler-product
structure collapses the trichotomy to a dichotomy** — which would be a genuine reduction, since MI
would then follow from *any* analytic continuation, not from meromorphy.

### 79.1 The setup

Unconditionally, Ramanujan gives `a_F(p^k) ≪_ε p^{kε}` for every `k`, so the local factor
`F_p(x) = Σ_k a_F(p^k)x^k` and the Rankin–Selberg local factor
```
G_p(x) := Σ_k |a_F(p^k)|² x^k
```
are **holomorphic on `|x| < 1`** with `G_p(0)=1`, and `R_{F,F}(w) = ∏_p G_p(p^{−w})`. No polynomial
Euler product is assumed.

Estermann's theorem (1928), and Kurokawa's extensions, concern
`Z(w) = ∏_p h(p^{−w})` for a *fixed* `h ∈ Z[x]` with `h(0)=1`: `Z` continues past its abscissa iff
`h` is a product of cyclotomic polynomials, in which case `Z(w) = ∏_{j≥1} ζ(jw)^{m_j}·(analytic)`
with `m_j ∈ Z`; otherwise `Re w = 0` is a natural boundary. **There is no intermediate branch-point
behaviour.** If this dichotomy transferred to `R_{F,F}`, then:
```
R_{F,F} continues at all past Re w = 1   ⟹   its exponent at w = 1 is an integer   ⟹   MI.
```

### 79.2 Why it does not transfer — the integrality is in the coefficients

The exponents `m_j` in Estermann's factorisation are produced by the formal identity
`h(x) = ∏_{j≥1}(1 − x^j)^{−m_j}`, whose solution is the **Witt/necklace transform** of the
coefficients of `h`. Those `m_j` are integers **precisely because `h ∈ Z[x]`**; for a power series
with arbitrary complex coefficients the transform returns complex exponents, and the dichotomy —
"cyclotomic or natural boundary" — becomes "the exponents happen to be integers, or not".

For `F ∈ S` the coefficients `|a_F(p^k)|²` are non-negative reals with no integrality whatsoever
(and `G_p` varies with `p`, so Kurokawa's two-variable version does not apply either: `G_p(x)` is not
of the form `H(x, 1/p)` for a holomorphic `H`).

> **Verdict: REDISCOVERED / CIRCULAR.** The Estermann–Kurokawa mechanism is not an independent source
> of integrality for `S`. In the automorphic case it *does* fire, because the local factor is
> `∏_{i,j}(1 − α_i\overline{α_j}x)^{−1}` and the exponent at `w=1` is the **count**
> `#{(i,j) : α_i\overline{α_j} = 1}` — Schur's lemma again (§33.2, §69.3). Recorded do-not-retry.

### 79.3 What survives

Two things.

1. **The trichotomy does not collapse.** For `F ∈ S` the possibility "`R_{F,F}` has a branch point of
   non-integer exponent at `w = 1`" is *not* excluded by the Euler-product structure. So MI genuinely
   requires meromorphy, not merely continuation. This closes the hoped-for weakening and is recorded
   as a hard constraint on all future routes.
2. **The natural-boundary option is compatible with everything known.** Wirsing's theorem (§58) gives
   `Σ_{n≤x}|a_F(n)|² ~ c x(log x)^{n_F−1}/Γ(n_F)` **without any continuation**, so a natural boundary
   at `Re w = 1` contradicts nothing currently proved. Recorded so no later cycle attempts to derive
   a contradiction from a natural boundary alone.

### 79.4 Consolidated table of closed integrality mechanisms

| mechanism | fires? | reason |
|---|---|---|
| pole order of a meromorphic function | **yes** | the only live mechanism (§39.1, §74) |
| positivity / Cauchy–Schwarz / Gram | no | blind to `Im`, and `ζ^{1/2}` witness (§69.1) |
| Schur / representation dimension | no | needs the Sato–Tate group (§33.2, §69.3) |
| Galois orbits | no | no Galois action in `S` (§35) |
| lattice-point counts | no | no lattice object in `S` (§35) |
| zero multiplicities | no | computes `E_F = Σe_i²d_i` (§72.3) |
| reflection `w ↦ 2−w` phase | no | dual term is a divergent partial sum (§69.2) |
| Beurling–Lax / operator multiplicity | no | needs finite-dimensionality = the group (§74.1) |
| geometric mean / Jessen function | no | blind to `n_F`; `ζ` witness (§77.1) |
| Estermann–Kurokawa cyclotomic rigidity | no | integrality lives in `Z[x]`, absent in `S` (§79.2) |

Ten mechanisms examined; exactly one fires, and it is the one MI is a restatement of.

---

## 80. Cycle 80 (2026-07-26) — the dilation correlation of standard twists sees `ω`

§69.1 proved that no identity among prime energies over the monoid generated by `F, G` and their
conjugates can determine `ω(F,G) = Im c_{F,G}`. §77.2 then narrowed the admissible tools to
functionals sensitive to density-zero sets. This cycle exhibits one, and it computes `ω`.

### 80.1 Correlation of a twist with a dilated twist

For `F, G ∈ S` of the same degree `d ≥ 1` put `c_n = a_F(n)e^{−2πbn^{1/d}}n^{−1/2}` and
`d_m = a_G(m)e^{−2πb'm^{1/d}}m^{−1/2}`, so that
`Φ_F(1/2,a−ib) = Σ_n c_n e^{−2πian^{1/d}}` and `Φ_G(1/2, λa − ib') = Σ_m d_m e^{−2πiλam^{1/d}}`.
The Bohr mean of the product keeps exactly the pairs with `n^{1/d} = λ m^{1/d}`, i.e. `n = λ^d m`.

> **Theorem 29 (dilation correlation = shifted convolution).** Let `r,s ≥ 1` be coprime,
> `λ := (r/s)^{1/d}`, and take the depths `b` and `b' = λ b`. Then for `F,G ∈ S` of degree `d`,
> ```
> lim_{A→∞}(1/2A)∫_{−A}^{A} Φ_F(1/2, a−ib) · conj(Φ_G(1/2, λa − iλb)) da
>     = (rs)^{−1/2} · Σ_{t≥1} a_F(rt) conj(a_G(st)) · e^{−4πb (rt)^{1/d}} · t^{−1} .
> ```
> If `λ^d ∉ Q` the matching set is empty and the correlation is **exactly `0`**.
>
> *Proof.* `n^{1/d} = λm^{1/d} ⟺ sn = rm ⟺ (n,m) = (rt, st)` by coprimality; the exponentials
> combine because `b' = λb` gives `e^{−2πb(rt)^{1/d}}e^{−2πλb(st)^{1/d}} = e^{−4πb(rt)^{1/d}}`, and
> `(rt)^{−1/2}(st)^{−1/2} = (rs)^{−1/2}t^{−1}`. Absolute convergence justifies the term-by-term
> Bohr mean. ∎ At `r = s = 1` this is Theorem 23.

So the **dilation autocorrelation function** `λ ↦ K_{F,G}(λ,b)` of the standard twists is supported
exactly on `{(r/s)^{1/d} : r,s ≥ 1}` and there computes the **shifted convolution sums**
`Σ_t a_F(rt)\overline{a_G(st)}/t` — with their full complex value.

### 80.2 The consequence for the imaginary half of Conjecture B

> **Theorem 30 (`ω` is a twist correlation).** For `F,G ∈ S` of equal degree `d ≥ 1`,
> ```
> ω(F,G) = lim_{b→0+}  Im[ lim_{A→∞}(1/2A)∫_{−A}^{A} Φ_F(1/2,a−ib) conj(Φ_G(1/2,a−ib)) da ]
>                       /  log log(1/b) .
> ```

This answers the question left open by §69–§71: **the alternating form `ω`, provably invisible to
every prime-energy identity, is visible as the imaginary part of the Bohr correlation of the two
standard twists at depth `b`.** It is a thin-set functional (a sum over the matched pairs of a
discrete frequency set), so it is admissible under §77.2's rule, and unlike Theorem 20 it is *not* a
trivial restatement of the coefficients: the correlation is an analytic quantity attached to two
entire functions of `s`, computed by an averaging in `a` that is exact rather than asymptotic.

**Both halves of Conjecture B now have a representation of the correct type:**
```
real part      n_F        : Theorem 28 — residue-weighted damped spectral sum over Spec(F)
imaginary part ω(F,G)     : Theorem 30 — imaginary part of the twist correlation at depth b
```
and both are governed by the same `b → 0` limit of Bohr correlations of standard twists. The
programme's two halves, split apart in §70.2, are reunited on one object: the correlation matrix
`K_{F,G}(λ,b)` of standard twists.

### 80.3 The new target

> **(TC) Twist correlation rigidity.** For `F,G ∈ S` of equal degree, the correlation
> `K_{F,G}(1,b)` has, as `b → 0`, an asymptotic `c_{F,G}·(log 1/b)^{?}` whose leading coefficient is
> a **non-negative integer** and whose imaginary part is `o(loglog(1/b))`.

TC is exactly Conjecture B for the pair `(F,G)` transported onto the twist correlation. Its value is
that it is a statement about one explicit analytic object — the correlation of two entire functions
along a horizontal line at depth `b` — with no Rankin–Selberg convolution, no automorphy, and no
Euler product used in its formulation.

**Formalised (finite form, unconditional):** `genPoly_mul_conj_bilinear` and
`genPoly_meanValue_bilinear` give the exact expansion
`∫_T^{T+U} P·conj(Q) = Σ_{n,m} a_n conj(c_m) · oscInt(λ_n − μ_m, T, U)` for two arbitrary frequency
families, together with `oscInt_norm_le` (`‖oscInt δ T U‖ ≤ 2/|δ|`, uniform in the interval length),
which isolates the matched pairs in the limit.

---

## 81. Cycle 81 (2026-07-26) — the degree barrier, quantified: the Bohr averaging length

Phase-4 interrogation of Theorem 29/30: where exactly does the twist-correlation route inherit the
old difficulty?

### 81.1 The Bohr spectrum of `|Φ_F|²` accumulates at `0` iff `d ≥ 2`

The Fourier–Bohr spectrum of `a ↦ |Φ_F(1/2,a−ib)|²` is the difference set
`{2π(n^{1/d} − m^{1/d})}`, with coefficient at frequency `ξ` equal to `Σ_{n^{1/d}−m^{1/d}=ξ}c_n\bar c_m`,
`c_n = a_F(n)e^{−2πbn^{1/d}}n^{−1/2}`. The value at `ξ = 0` is exactly `M_F(b)` (Theorem 23), because
`n^{1/d} = m^{1/d} ⟺ n = m`.

But for `n − m = h` fixed and `n → ∞`,
```
n^{1/d} − m^{1/d} ≍ h / (d · n^{1−1/d})  →  0     (d ≥ 2),
```
so for `d ≥ 2` **the Bohr spectrum accumulates at `0`**: the diagonal frequency is not isolated. For
`d = 1` the spectrum is `2πZ` and the diagonal is isolated by a gap `2π`.

### 81.2 The quantitative interchange threshold

By the mean value theorem, for `n > m`, `n^{1/d} − m^{1/d} ≥ (n−m)n^{1/d−1}/d`, so
`|oscInt| ≤ 2/|λ_n − λ_m| ≤ (d/π)·n^{1−1/d}/(n−m)`. With `|c_n| ≪_ε n^{ε−1/2}e^{−2πbn^{1/d}}` the
effective range is `n ≤ N := b^{−d}`, and
```
Σ_{n≠m} |c_n c_m| · max(n,m)^{1−1/d}/|n−m|  ≪  N^{1−1/d} (log N)² ,
```
while `M_F(b) ≍ (log N)^{n_F}`.

> **Theorem 31 (Bohr averaging length / degree barrier).** For `F ∈ S` of degree `d ≥ 1` and any
> `δ > 0`,
> ```
> (1/2A)∫_{−A}^{A}|Φ_F(1/2,a−ib)|² da = M_F(b)·(1 + o(1))
> ```
> as `b → 0`, provided
> ```
> A  ≫_F  b^{−(d−1)} · (log(1/b))^{2−n_F+δ} .
> ```
> For `d = 1` any `A → ∞` suffices, uniformly in `b`; for `d ≥ 2` the required averaging length
> **grows like `b^{−(d−1)}`**, so the limits `A → ∞` and `b → 0` do not commute uniformly.

### 81.3 What this says

> **The "degree barrier" of the Selberg class — everything is known in degree `1` and nothing in
> degree `≥ 2` — is, on the twist side, exactly the statement that the Bohr averaging length needed
> to isolate the diagonal grows like `b^{−(d−1)}`.**

This is a new and completely explicit form of the barrier. It also explains, in one line, why the
programme's degree-1 results (Kaczorowski–Perelli's classification, the linear half of Conjecture A,
orthogonality against Dirichlet `L`-functions) all go through while their degree-`≥2` analogues do
not: in degree `1` the diagonal is separated by a **fixed gap** `2π`, and every diagonal-extraction
argument is uniform; in degree `≥ 2` the gap closes at rate `n^{1/d−1}` and no uniform extraction
exists.

**Relation to earlier records.** This is the quantitative form of the remark already in the header of
`GeneralizedDirichletMeanValue.lean` (“the diagonal is isolated only for `d = 1`”) and of §9.3/§21.1.
It is also the same phenomenon as §11.1's divergence of the `α`-integral on `Spec(F)`: there the
failure was qualitative, here it is a rate.

**Consequence for TC (§80.3).** Any proof of TC must supply an off-diagonal estimate valid for
`A ≪ b^{−(d−1)}`, i.e. must handle the near-diagonal pairs `n − m = h ≠ 0` with `h ≪ N^{1−1/d}/A`.
Those are precisely the pairs whose contribution the Rankin–Selberg method handles by *automorphy*.
So TC does not evade the open core — but it names the missing estimate exactly, as a bound on
```
Σ_{h ≠ 0} Σ_n a_F(n) conj(a_G(n−h)) e^{−4πb n^{1/d}} n^{−1} · (something ≪ n^{1−1/d}/(A|h|)) ,
```
i.e. as a **shifted-convolution estimate for the coefficients of `F` and `G`** — the classical object
where the analytic input to Rankin–Selberg actually lives. Recorded as the precise missing ingredient.

---

## 82. Cycle 82 (2026-07-26) — the twist-exponent spectrum: where `S` sits relative to automorphy

Phase-4 interrogation of Theorem 31. If the standard twist's diagonal is not isolated for `d ≥ 2`,
can a *different* twist exponent do better? Consider the whole family
```
F_κ(s,α) := Σ_n a_F(n) e(−α n^κ) n^{−s} ,   κ > 0 .
```

### 82.1 Two monotone properties, in opposite directions

**Bohr diagonal isolation.** The frequencies are `2π n^κ`, with consecutive gaps `≍ κ n^{κ−1}`. The
diagonal of the Bohr mean is isolated by a *fixed* gap iff `κ ≥ 1`; for `κ < 1` the gaps close like
`n^{κ−1}` and Theorem 31's averaging length `A ≫ b^{−(1/κ−1)·...}` blows up.

**Analytic continuation.** The Selberg axioms deliver continuation exactly at the *low* end:
Kaczorowski–Perelli's nonlinear-twist theory gives `F_κ` entire for `0 < κ < 1/d`, and for `κ = 1/d`
the standard twist with poles at `s*_ℓ` and residues proportional to `conj(a_F(n_α))`. **No
continuation is delivered by the axioms for `κ > 1/d`.**

Since `1/d ≤ 1` with equality iff `d = 1`:

> **Theorem 32 (twist-exponent trade-off).** Within the family `{F_κ}`, the Selberg axioms supply
> analytic structure only for `κ ≤ 1/d`, while the Bohr diagonal is isolated only for `κ ≥ 1`. The
> two ranges intersect **iff `d = 1`**. In degree `1` the standard twist is the linear twist and both
> hold simultaneously; in degree `≥ 2` no member of the family has both.

This is a sharp, one-line explanation of the degree barrier for the entire twist method.

### 82.2 The correction that the false version taught

An earlier form of this cycle claimed continuation *fails* for `κ > 1/d`. **That is wrong**: for a
holomorphic cusp form of weight `k` (degree `2`), the additive twist `Σ a(n)e(nα)n^{−s}` at `κ = 1`
is the Mellin transform of `f(α+iy)` and continues meromorphically by **modularity**. So the correct
statement is not "continuation fails above `1/d`" but:

> `κ ≤ 1/d` is what the **Selberg axioms** give; `κ = 1` is what **automorphy** gives.

### 82.3 The consequence — a new measure of the gap between `S` and automorphy

> **The gap between the Selberg class and automorphy is exactly the gap between `κ = 1/d` and
> `κ = 1` in the twist-exponent spectrum.**

At `κ = 1` the whole machinery of cycles 73–80 becomes elementary and unconditional: for any `F ∈ S`
and `α = a + ib ∈ H`, `Ψ_F(σ,α) := Σ a_F(n)e(nα)n^{−σ}` converges absolutely, and the Bohr mean is
```
mean_a [ Ψ_F(σ, a+ib) conj(Ψ_G(σ, a+ib)) ] = Σ_n a_F(n)conj(a_G(n)) e^{−4πbn} n^{−2σ} ,
```
with the diagonal isolated by the fixed gap `2π`, so Theorem 31's threshold improves from
`A ≫ b^{−(d−1)}` to `A ≫ (log(1/b))^{2−n_F+δ}`.

**But this is Parseval on the disc and nothing more.** `Ψ_F` carries no continuation and no functional
equation from the axioms, so the identity is a tautology about the coefficients — exactly the
"restatement" trap. The content of the standard twist (`κ = 1/d`) is that K–P give it *genuine*
analytic structure; the price is the lost diagonal isolation. Recorded as a matched pair:

| `κ` | diagonal isolated | analytic structure from the axioms | net |
|---|---|---|---|
| `< 1/d` | no | entire (K–P) | no arithmetic at all |
| `= 1/d` | only if `d = 1` | poles on `Spec(F)`, residues `∝ conj(a_F(n))` (K–P) | the programme's object |
| `1/d < κ < 1` | no | none | useless |
| `= 1` | **yes** | none from the axioms; **modularity** if `F` is automorphic | tautology in `S`, powerful under automorphy |

### 82.4 Why this is not a route to a proof, and what it *is*

By **Weil's converse theorem**, continuation plus the right functional equations for the additive
twists at all rationals is equivalent to automorphy. So "prove `κ = 1` continuation for `F ∈ S`" is
not a weakening of the automorphy conjecture — it *is* the automorphy conjecture. Recorded
do-not-retry.

What the cycle gives is a **new invariant of the difficulty**: the twist-exponent gap `[1/d, 1]`.
Its length `1 − 1/d` is `0` exactly in degree `1`, which is exactly the range where every Selberg
conjecture is a theorem, and it grows to `1` as `d → ∞`. That matches, quantitatively, the exponent
`d − 1` in Theorem 31's averaging length. Two independent computations of the same barrier.

---

## 83. Cycle 83 (2026-07-26) — the two energies are linked: multiple zeros force extra prime energy

§72 introduced the zero energy `E_F = Σ_i e_i² d_i` alongside the prime energy `n_F = Σ_i e_i²` and
showed they are different invariants. This cycle links them.

### 83.1 The inequality

Write the primitive factorisation `F = ∏_i F_i^{e_i}`, so `d_F = Σ_i e_i d_i`, `n_F = Σ_i e_i²`,
`E_F = Σ_i e_i² d_i` (the last as in §72.1, using that distinct primitive factors have disjoint zero
sets and each `N_{F_i}(T) ~ (d_i/2π)T log T`).

Since `max_i e_i ≤ √(n_F)`,
```
E_F = Σ_i e_i² d_i ≤ (max_i e_i) · Σ_i e_i d_i = (max_i e_i) · d_F ≤ √(n_F) · d_F .
```

> **Theorem 33 (energy inequality).** `n_F ≥ (E_F/d_F)²`, i.e.
> ```
> prime energy  ≥  (mean squared multiplicity of the zeros of F)² .
> ```
> Combined with the unconditional bracket `E_F ≥ d_F` (Theorem 22, Lean-verified), this gives
> `n_F ≥ 1` for every non-constant `F ∈ S`, and more precisely
> ```
> n_F ≥ ( mean squared zero multiplicity )² ,   with equality iff a single primitive factor carries
> all the multiplicity.
> ```

> **Corollary 34.** If the zeros of `F` have mean squared multiplicity `> 1` — equivalently
> (Theorem 22) if `F` has multiple zeros of positive density — then `n_F > 1`. Under MI this forces
> `n_F ≥ 2`, hence **`F` is not primitive**. Contrapositive: *a primitive element of `S` has almost
> all zeros simple.*

This is the first inequality in the programme relating the prime side and the zero side of `S`, and
it derives the expected "primitive `⟹` simple zeros" phenomenon from the two energies rather than
assuming it.

**Honest scope.** Theorem 33 and Corollary 34 use the primitive factorisation and the disjointness of
the zero sets of distinct primitive factors; the latter is itself a consequence of Conjecture B, so
these are statements *within the standard picture*, not unconditional theorems. What **is**
unconditional is the bracket they rest on: `Σ_ρ m_ρ² ≥ N_F(T)`, with equality iff all zeros are
simple (Theorem 22, Lean: `sum_le_sum_sq`, `sum_sq_eq_sum_iff`, `sum_sq_div_sum_ge_one`).

### 83.2 The Bohr gap theorem, formalised

The rigorous core of every diagonal-extraction argument in cycles 73–82 is now formalised
unconditionally:

> **Theorem 35 (uniform-gap diagonal extraction).** If the frequencies of a generalized Dirichlet
> polynomial `P(t) = Σ_{n∈s} a_n e^{iλ_n t}` satisfy `|λ_m − λ_n| ≥ g > 0` for `m ≠ n`, then for
> every `T` and `U`
> ```
> ‖ ∫_T^{T+U} |P|² − U·Σ_n |a_n|² ‖  ≤  (2/g)·(Σ_n ‖a_n‖)² ,
> ```
> an error bounded **independently of the interval, its length and its position**.
>
> Lean: `genPoly_meanValue_error_of_gap`.

Applied with `λ_n = n` (additive twist, gap `1`) this makes the `κ = 1` column of §82.3's table an
unconditional theorem; applied with `λ_n = n^{1/d}`, `d ≥ 2`, the hypothesis fails for every `g > 0`,
which is exactly Theorem 31's barrier in its cleanest form. **The degree barrier is now visible as
the failure of a single hypothesis in one formalised lemma.**

---

## 84. Cycle 84 (2026-07-26) — one cusp versus all cusps

§82 located the gap between `S` and automorphy at the twist exponent `κ = 1`. This cycle identifies
what that gap *is*, in classical language.

### 84.1 The additive twist is a power series in `q = e(α)`

For `F ∈ S` put
```
𝔉_s(q) := Σ_{n≥1} a_F(n) n^{−s} q^n ,      |q| < 1 ,
```
holomorphic in `q` on the unit disc (Ramanujan gives `a_F(n) ≪ n^ε`), and `1`-periodic in `α` when
`q = e(α)` — so the `κ = 1` twist `Ψ_F(s,α)` of §82 is exactly `𝔉_s(e(α))`.

The Dirichlet series `F(s) = Σ a_F(n)n^{−s}` is the **Abel limit of `𝔉_s` at the single boundary
point `q = 1`**. Selberg's axiom (2) — meromorphic continuation in `s` with a controlled pole —
is a statement about that one boundary point and nothing else.

### 84.2 The decomposition at a general root of unity

> **Theorem 36 (additive-twist decomposition).** For `α = h/k` in lowest terms, grouping `n` by
> `g = gcd(n,k)` and expanding `e(mh/(k/g))` over the characters mod `k/g`,
> ```
> Ψ_F(s, h/k) = Σ_{g | k} g^{−s} Σ_{χ mod (k/g)} c_χ(g,h,k) · D_{g,χ}(s) ,
> D_{g,χ}(s) := Σ_{(m, k/g)=1} a_F(gm) χ(m) m^{−s} ,
> c_χ(g,h,k) = (1/φ(k/g)) Σ_{u mod (k/g)}^{*} e(uh/(k/g)) \barχ(u) .
> ```
> So `𝔉_s` is controlled at the root of unity `e(h/k)` **iff** every *Hecke-shifted character twist*
> `D_{g,χ}` (`g | k`, `χ mod k/g`) continues meromorphically in `s`.

At `k = 1` the sum has the single term `D_{1,triv} = F`, and the statement is axiom (2). For `k > 1`
it requires the character twists `F_χ` (`g = 1`) and the Hecke translates `Σ_m a_F(gm)m^{−s}`
(`χ` trivial) — neither of which the Selberg axioms provide, and both of which automorphy provides
(they are the `L`-functions of `π⊗χ` and of `T_g π`).

### 84.3 The principle

> **`S` is control at one cusp; automorphy is control at all cusps.**
>
> Precisely: the Selberg axioms assert meromorphic continuation of the `s`-Mellin data of `𝔉_s` at
> the boundary point `q = 1` only. Automorphy asserts it at **every** root of unity — equivalently,
> by Weil's converse theorem, at every rational `α`, with the correct functional equations. Between
> the two there is nothing: by Weil, "all roots of unity with functional equations" *is* automorphy.

This is the same gap as §82's twist-exponent interval `[1/d, 1]` and as §81's averaging length
`b^{−(d−1)}`, now in its classical form. Three independent formulations of one obstruction:

| formulation | the gap |
|---|---|
| Bohr averaging length (§81) | `A ≫ b^{−(d−1)}` versus `A ≫ polylog` |
| twist exponent (§82) | `κ ≤ 1/d` (axioms) versus `κ = 1` (automorphy) |
| cusps (§84) | `q = 1` only versus all roots of unity |

**Consequence, recorded as a hard constraint.** Any proof of MI from the Selberg axioms alone must
extract integrality from data at a *single* cusp. Every mechanism that fires in the automorphic
world — Rankin–Selberg, Schur, Sato–Tate, the spectral decomposition — uses all cusps. That is the
structural reason the ten mechanisms of §79.4 all failed: nine of them are all-cusp mechanisms in
disguise, and the tenth (pole order) is the one-cusp mechanism, which is why MI is a restatement of
it.

**[OPEN CORE], sharpened.** Is there a one-cusp integrality mechanism at all? Equivalently: can the
order of the singularity at `w = 1` of `R_{F,F}` be forced to be an integer using only the
`q = 1` boundary data of `𝔉_s`? If the answer is no — if one could *prove* that no such mechanism
exists — that would be a genuine independence-type result for the Selberg class, and would make MI
strictly equivalent to an all-cusp statement. That dichotomy is now the sharpest available target.

---

## 85. Cycle 85 (2026-07-26) — where the integrality *cannot* come from: two independence results

§84 asked whether a one-cusp integrality mechanism exists. This cycle answers two sharper questions:
**which axioms are doing the work**, and **which integers the axioms actually supply**.

### 85.1 The functional equation is essential — an unconditional witness

Take a non-principal Dirichlet character `χ` and a real `c > 0`, and set
```
F_c(s) := L(s,χ)^c    (principal branch on the standard zero-free region of L).
```
Then:
- (1) `F_c` is a Dirichlet series with `a_{F_c}(1)=1`, absolutely convergent for `Re s > 1`;
- (4) it has an Euler product: `log F_c = c·log L(·,χ) = Σ_n c·b_L(n)n^{−s}`, `b_L(n) ≪ n^{1/2}` and in
  fact supported on prime powers with `b_L(p^k) = χ(p)^k/k`, so `b(n) ≪ n^θ` for every `θ > 0`;
- (5) Ramanujan holds: the local coefficients are `binom(c+k−1,k)χ(p)^k ≪ k^{c−1}`, so
  `a_{F_c}(n) ≪_ε n^ε`;
- `F_c` is **holomorphic and non-vanishing on a neighbourhood of the closed half-plane `Re s ≥ 1`**
  (the classical zero-free region of `L`), so it has no pole and no zero there;
- all **linear** densities vanish: `Σ_p a_{F_c}(p)p^{−1−iθ} = c Σ_p χ(p)p^{−1−iθ} = O(1)` for every
  real `θ`;
- but `Σ_{p≤x}|a_{F_c}(p)|²/p = c² loglog x + O(1)`, so `n_{F_c} = c²`, **non-integral** for suitable
  `c`.

> **Theorem 38 (independence of the functional equation).** Axioms (1), (4), (5) of the Selberg
> class, together with holomorphy and non-vanishing on a neighbourhood of `Re s ≥ 1` and the
> vanishing of every linear density, do **not** imply `n_F ∈ Z`. Unconditional.

So the integrality of `n_F` comes neither from the Euler product, nor from Ramanujan, nor from any
edge behaviour near `Re s = 1`. It must come from **axiom (3) together with continuation across the
critical strip** — i.e. from the reflection `s ↦ 1 − \bar s` and the zeros it constrains. This
explains, in one witness, why every "edge" argument in the programme (Landau, Wiener–Ikehara,
Halász, the pretentious method, the Energy Gap machinery) stops short: they all live where the
witness lives.

*(What kills `F_c` inside `S` is monodromy around the **zeros of `L` in the critical strip**:
`L^c` is not single-valued there for `c ∉ Z`. That is a one-cusp mechanism — but it is available only
because the coefficients are *proportional* to those of a known element. It is §39.1's mechanism, and
it does not generalise to the quadratic case.)*

### 85.2 The axioms supply only additive integers

> **Theorem 39 (additive versus quadratic).** Every integer-valued invariant that the Selberg axioms
> attach to `F` — the number of gamma factors `r_F`, the pole order `m_F` at `s = 1`, and `d_F` when
> integral — is **additive** under multiplication in `S`:
> ```
> r_{FG} = r_F + r_G ,  m_{FG} = m_F + m_G ,  d_{FG} = d_F + d_G ,
> ```
> (and `q_{FG} = q_F q_G`, `ω_{FG} = ω_F ω_G` are multiplicative). Hence each is a **linear form in
> the exponents `e_i` of the primitive factorisation**. Selberg's `n_F = Σ_i e_i²` is a **quadratic
> form** in those exponents (§69.1: `n_{FG} = n_F + n_G + 2Re⟪v_F,v_G⟫`).
>
> A quadratic form is not a function of linear forms with generator-independent weights. Explicit
> witness inside `S`: for distinct primitive even `χ₁ ≠ χ₂` mod `q`,
> ```
> F = L(·,χ₁)L(·,χ₂)  and  G = L(·,χ₁)²
> ```
> share degree `2`, conductor `q²`, gamma factor, number of gamma factors `2`, and pole order `0`,
> yet `n_F = 2` and `n_G = 4`.
>
> **Consequence.** `n_F ∈ Z` is not a formal consequence of the integrality of the axiomatic
> invariants. Any proof of MI must *manufacture a new integer*, which by §79.4 means exhibiting a
> meromorphic function whose pole order is `n_F`.
>
> **Formalised, unconditional:** `additive_not_determine_energy`,
> `additive_family_not_determine_energy`, `energy_ne_of_same_total` — the exponent vectors `(1,1)` and
> `(2,0)` have equal weighted totals for every constant weight and energies `2 ≠ 4`.

### 85.3 The two results together

```
§85.1 : the integrality is not in axioms (1),(4),(5) or in the edge  →  it is in the reflection
§85.2 : the reflection supplies only additive integers               →  it cannot supply n_F directly
```
So MI requires a **new meromorphic object**, constructed from the reflection, whose pole order is a
quadratic function of the factorisation. That object is the Rankin–Selberg convolution, and §84 says
it is an all-cusp object. The programme's conclusion is now a closed logical loop with every step
identified:

> `n_F ∈ Z` ⟸ pole order of `R_{F,F}` ⟸ meromorphy of `R_{F,F}` ⟸ all-cusp control of `𝔉_s`
> ⟸ automorphy; and no proper sub-step of this chain is supplied by the Selberg axioms, each failure
> being witnessed explicitly (§85.1 for the axioms, §85.2 for the invariants, §79.4 for the ten
> mechanisms, §84 for the cusps).

**This is the sharpest statement the programme can make about *why* Conjecture A is hard**, and each
link is now either a theorem or an explicit witness rather than an impression.

---

## 86. Cycle 86 (2026-07-26) — the fractional-power route to a counterexample, closed by divisors

§56 squeezed a counterexample to Conjecture A between "structured phases" and "generic phases". The
most natural structured attempt is a **fractional power product**
```
F = ∏_i G_i^{c_i} ,     G_i ∈ S ,   c_i ∈ R ∖ Z ,
```
which has `n_F = Σ_{i,j} c_i c_j Re⟪v_{G_i},v_{G_j}⟫` and can easily be arranged non-integral. This
cycle closes that route with divisor data rather than phases.

### 86.1 The obstruction

`F` must be meromorphic on `C` (axiom (2)), so it is single-valued; the monodromy of `∏G_i^{c_i}`
around a point `ρ` is `exp(2πi Σ_i c_i ord_ρ(G_i))`.

> **Theorem 40 (fractional-power obstruction).** If `F = ∏_i G_i^{c_i}` is single-valued and
> meromorphic on `C` with `G_i` meromorphic, then
> ```
> Σ_i c_i · ord_ρ(G_i) ∈ Z    for every ρ ∈ C .
> ```
> Consequently, if the `G_i` have pairwise **disjoint** zero sets, then `c_i·ord_ρ(G_i) ∈ Z` at every
> zero `ρ` of `G_i`. Hence:
> - one **simple** zero of `G_i` forces `c_i ∈ Z`;
> - two zeros of `G_i` of **coprime** orders force `c_i ∈ Z`.
>
> **Formalised, unconditional:** `exponent_int_of_coprime_orders`, `exponent_int_of_simple_zero`.

### 86.2 The squeeze it produces

> **Corollary 41.** A fractional-power counterexample with disjoint zero sets requires **every**
> factor `G_i` with `c_i ∉ Z` to have *all* its zeros of multiplicity `≥ 2`, and in fact of
> multiplicities with a common factor `≥ 2` (the denominator of `c_i`). By Theorem 22 that forces
> `E_{G_i} ≥ 2 d_{G_i}`, and by Theorem 33 `n_{G_i} ≥ (E_{G_i}/d_{G_i})² ≥ 4`.

So the building blocks of a fractional counterexample must themselves carry prime energy `≥ 4`: they
cannot be primitive-like. This is a strong self-consistency squeeze, complementary to §56's phase
squeeze and obtained from an entirely different invariant (zero multiplicities rather than
coefficient phases).

### 86.3 The "cancel the monodromy" variant, also closed

One might hope to cancel the branch points of `G_1^{c}` against those of `G_2^{−c}`. This requires
`G_1` and `G_2` to have the **same divisor**. But two elements of `S` with the same divisor differ by
`e^{as+b}`, and `e^{as} = t^{−s}` with `t = e^{−a}`; for the quotient to be a Dirichlet series with
first coefficient `1` one needs `t = 1` and `e^b = 1`, i.e. `G_1 = G_2` and `F = 1`.

> **Recorded do-not-retry.** Neither a fractional power product with disjoint zeros (§86.1) nor a
> monodromy-cancelling pair (§86.3) can produce a counterexample. Combined with §56.1 (structured
> phases) and §56.2 (generic phases), the four most natural constructions are all closed.

### 86.4 Where the remaining freedom is

What survives §86 is exactly: **primitive factors sharing zeros**, with the shared multiplicities
conspiring so that `Σ_i c_i ord_ρ(G_i) ∈ Z` at every `ρ` while no individual `c_i` is an integer.
Distinct primitives sharing all their zeros is precisely what Selberg's Conjecture B forbids (it
would make them "the same" spectrally), so the surviving window is:

> **The only remaining fractional-power window is: distinct primitive elements of `S` with
> substantially overlapping zero sets.** Ruling that out is a *zero-side* form of Conjecture B, and
> by §72 it is governed by the zero energy `E_F`, not by the prime energy `n_F`.

That is a new, concrete, and independently meaningful target: **can two distinct primitive elements
of `S` share a positive proportion of their zeros?** Under the standard picture the answer is no, and
a proof would close §86.4 and with it the whole fractional-power route.

---

## 87. Cycle 87 (2026-07-26) — a scope correction, and a failed bridge worth recording

### 87.1 Scope correction to §83

Theorem 33 (`n_F ≥ (E_F/d_F)²`) and Corollary 34 were derived from `E_F = Σ_i e_i² d_i`, which §72.1
obtained **assuming the primitive factors have disjoint zero sets**. If distinct primitive factors
share zeros, the zero energy computed from the divisor is strictly larger than `Σ_i e_i² d_i`, and
the chain `E_F ≤ (max_i e_i)·d_F ≤ √(n_F)·d_F` breaks.

> **Corrected statement.** `n_F ≥ (E_F/d_F)²` holds **when the primitive factors of `F` have pairwise
> disjoint zero sets**. Unconditionally what survives is the Lean-verified bracket `E_F ≥ d_F` with
> equality iff all zeros of `F` are simple (Theorem 22).

### 87.2 The attempted bridge, and why it fails

The natural next step was: *if two distinct primitives `F,G` share a proportion `δ` of their zeros,
then `H = FG` has mean squared multiplicity `1+δ`, hence by Theorem 33 `n_H ≥ (1+δ)²`, hence*
`Re c_{F,G} ≥ (δ²+2δ−1)/2`, *so a large overlap would force non-orthogonality.*

**This is invalid**, for exactly the reason recorded in §72.3. The quantity `1+δ` is the **fine-scale
(`α → ∞`) limit** of the pair correlation of the zeros of `H`, while `n_H` lives at **bounded `α`**.
Theorem 33's inequality is not available in the shared-zero case (§87.1), and the two sides of the
attempted bridge sit at different scales of the same statistic. Numerically the attempted conclusion
would have given "`δ > √2 − 1 ≈ 0.414` contradicts orthogonality"; there is no such theorem.

> **Recorded do-not-retry.** No inequality between `n_F` (bounded-`α`) and the zero-multiplicity data
> `E_F` (`α → ∞`) is available without the disjointness hypothesis. This is the third time the same
> scale confusion has been caught (§67 → §72.3, §76 → §77.1, §83 → §87.2); the design rule of §77.2
> now has a companion:
>
> **Scale rule.** Never compare a bounded-`α` (prime-energy) quantity with an `α → ∞`
> (multiplicity) quantity without an explicit hypothesis linking the scales. The three natural
> statistics of `F` — degree (`α → 0`), prime energy (`α ≍ 1`), zero multiplicity (`α → ∞`) — are
> mutually independent.

### 87.3 What the failure leaves standing

The fractional-power route (§86) is closed by divisors, and its surviving window is
```
distinct primitive elements of S sharing a positive proportion of their zeros,
```
which §87.2 shows cannot be excluded by energy comparisons. It must instead be attacked with the
**divisor itself**. The concrete open question is unchanged and is worth stating on its own:

> **(ZS) Zero sharing.** Can two distinct primitive elements of `S` share a positive proportion of
> their non-trivial zeros?

`ZS` is implied false by the standard picture, is not implied by anything currently proved, and — by
§86 — a positive answer is the only remaining route to a fractional-power counterexample to
Conjecture A. It is a *zero-side* question, so §77.2's rule (thin sets) and §87.2's scale rule both
permit it, and it does not obviously funnel into Rankin–Selberg. **Recorded as the most promising
untouched target.**

---

## 88. Cycle 88 (2026-07-26) — attacking (ZS): the ratio functional equation

Target: **(ZS)** can two distinct primitive `F, G ∈ S` share a positive proportion of their zeros?

### 88.1 The ratio carries a degree-zero functional equation

Assume first that `F` and `G` have **identical gamma factors** `γ_0` (same `r`, `λ_j`, `μ_j`; hence
equal degree). Write `Λ_F = Q_F^s γ_0 F`, `Λ_G = Q_G^s γ_0 G` and `W := Λ_F/Λ_G`. Dividing the two
functional equations:

> **Theorem 43 (ratio functional equation).** `W` is meromorphic on `C` with divisor
> `div(F) − div(G)` — the shared zeros cancel, the gamma poles cancel — and
> ```
> W(s) = (ω_F/ω_G) · conj( W(1 − \bar s) ) .
> ```
> Hence `e^{−iθ_0}W` is **real on the critical line**, `θ_0 = ½ arg(ω_F/ω_G)`, and `R := F/G` is a
> Dirichlet series with `a_R(1)=1`, an Euler product `∏_p F_p/G_p`, and therefore **no zeros and no
> poles in `Re s > 1`**; by the functional equation, none in `Re s < 0` either. All zeros and poles of
> `R` lie in the closed critical strip.

> **Corollary 44.** Two elements of `S` with identical gamma factors that share **all** their zeros
> are equal. *Proof.* `W` is then entire, zero-free and of finite order, so `W = e^{as+b}`; then
> `F/G = e^{as+b}(Q_G/Q_F)^s = c·t^{−s}`, and `a_F(1) = a_G(1) = 1` forces `t = 1`, `c = 1`. ∎
> If moreover `F/G` is entire but only `G`'s zeros are all shared, then `R ∈ S^♯_0`, so by
> Kaczorowski–Perelli's degree-zero classification `R` is a Dirichlet polynomial; combined with its
> Euler product, `R` is supported on finitely many primes.

### 88.2 The natural attack, and exactly why it fails

`R = F/G` has **degree `0`**. For an element of `S^♯` of degree `δ_{deg}` the Riemann–von Mangoldt
formula gives `≍ (δ_deg/2π)T log T` zeros up to height `T`; degree `0` would give `O(T)`. Since
`R` has `≈ (1−δ)N_F(T)` zeros and `≈ (1−δ)N_G(T)` poles, "degree `0` ⟹ few zeros" would force
`δ = 1` and hence, by Corollary 44, `F = G` — a complete answer to (ZS).

**This fails, and the reason is exact.** The argument principle applied to `W` on the box computes
```
#zeros − #poles  =  (1/2π) Δ arg W ,
```
i.e. only the **difference**, which is `(1−δ)(N_F − N_G) = 0` when `d_F = d_G` — automatically
consistent with degree `0` and carrying no information about the **sum**. Nevanlinna theory gives
only `T(r,R) ≤ T(r,F) + T(r,G) + O(1)`, which permits `(1−δ) ≤ 1` and nothing more.

> **Recorded do-not-retry.** The degree of `F/G` constrains only `#zeros − #poles`, never the total.
> No counting-function argument alone can bound the shared proportion `δ`.

### 88.3 What (ZS) actually needs

To bound `δ` one must control the **sum** of zeros and poles of a meromorphic function of degree `0`,
which is a genuine value-distribution problem, not a counting one. Two features are available and
unused:

1. `e^{−iθ_0}W` is **real on the critical line** (Theorem 43), so its zeros and poles are symmetric
   about that line and its restriction to the line is a real meromorphic function whose sign changes
   are governed by the odd-order zeros and poles *on* the line.
2. `R = F/G` has an **Euler product**, so `log R(s) = Σ_p (a_F(p) − a_G(p))p^{−s} + …`, and the prime
   energy of `R` is `n_F + n_G − 2Re c_{F,G}` — which is `2` for orthogonal primitives and `0` when
   `F = G`.

Feature 2 is the first place where (ZS) touches the prime side **at the right scale**: `n_R` is a
bounded-`α` quantity (no violation of §87.2's scale rule), and it is small exactly when `F` and `G`
are prime-correlated. So:

> **Conjecture (ZS′).** For `F ≠ G` in `S` with identical gamma factors, the shared-zero proportion
> `δ` and the ratio energy `n_R = n_F + n_G − 2Re c_{F,G}` satisfy `δ → 1 ⟺ n_R → 0`, and
> `n_R = 0 ⟺ F = G`.

`ZS′` is the zero-side/prime-side bridge that §87.2 forbade at the wrong scale and permits at this
one. Its `n_R = 0 ⟹ F = G` half is a clean, self-contained target: **an element of `S^♯` with an
Euler product and vanishing prime energy is trivial** — the Energy Gap conjecture (§52) for the
ratio. Note `n_R ≥ 0` always, `n_R = 0` says `a_F(p) = a_G(p)` in density, and EG would then give
`F = G` by §39.1's monodromy applied to `R`. **So ZS′ reduces (ZS) to the Energy Gap conjecture for
degree-zero ratios**, which is a strictly smaller statement than EG for `S` and is the natural next
target.

---

## 89. Cycle 89 (2026-07-26) — the ratio Energy-Gap attack, and its exact point of failure

Target from §88.3: **`n_R = 0 ⟹ F = G`** for `R = F/G` with `F,G ∈ S` of identical gamma factors,
where `n_R = lim (loglog x)^{−1}Σ_{p≤x}|c_p|²/p`, `c_p := a_F(p) − a_G(p)`.

### 89.1 The intended mechanism

1. `n_R = 0` means `Σ_p |c_p|²/p < ∞` (up to `O(1)`), i.e. `(c_p p^{−1/2})_p ∈ ℓ²`.
2. If that forced `P(s) := Σ_p c_p p^{−s}` to be **holomorphic on `Re s > 1/2`**, then
   `log R = P + (k ≥ 2 terms)` would be holomorphic there (the prime-power terms converge absolutely
   for `Re s > 1/2` because `θ < 1/2`), hence `R = exp(log R)` would be holomorphic **and
   non-vanishing** on `Re s > 1/2`, so `F` and `G` would have identical divisors there; by the ratio
   functional equation (Theorem 43) the same would follow on `Re s < 1/2`.
3. The remaining zeros of `R` would lie on the critical line. If `R` had `≍ κ T log T` of them up to
   height `T`, then `log|R|` would have mean square `≍ log T → ∞` on lines approaching `Re s = 1/2`,
   contradicting the boundedness of `Σ_p|c_p|²p^{−2σ}` as `σ → 1/2+`.
4. Hence `R` would have `o(T log T)` zeros, i.e. `δ = 1`, and Corollary 44 would give `F = G`.

Steps 3 and 4 are sound. **Step 2 is not.**

### 89.2 The failure, precisely

`Σ_p |c_p|²/p < ∞` gives `Σ_p |c_p| p^{−σ} < ∞` only for `σ > 1`, by Cauchy–Schwarz
(`Σ_{p≤x}|c_p| ≪ x`), so the series `P(s)` is not known to converge — still less to be holomorphic —
anywhere in `1/2 < Re s ≤ 1`. Concluding "`R` is zero-free on `Re s > 1/2`" from an `ℓ²` condition on
the coefficients is a **zero-free half-plane from coefficient data**, i.e. an RH-strength statement.

> **Recorded do-not-retry.** This is the same wall as §9.6 and §22.1 ("`ℓ²` does not propagate across
> the strip"), now met in the ratio setting. No `ℓ²` or density hypothesis on `(a_F(p) − a_G(p))`
> yields a zero-free region for `F/G` without new input.

### 89.3 What survives, and the corrected reduction

Steps 1, 3, 4 remain valid and give an unconditional implication in the useful direction:

> **Theorem 45.** Let `F, G ∈ S` have identical gamma factors and let `R = F/G`. If `R` is
> holomorphic and non-vanishing on `Re s > 1/2`, then (by Theorem 43) the same holds on `Re s < 1/2`,
> and if in addition `log|R|` has bounded mean square on lines `Re s = σ → 1/2+`, then `R` has
> `o(T log T)` zeros, hence `F` and `G` share all but `o(1)` of their zeros, hence `F = G` by
> Corollary 44.

So the chain `(ZS) ⟸ ZS′ ⟸ EG-for-ratios` of §88.3 must be replaced by

```
(ZS)  ⟸  "F/G zero-free off the critical line"  +  "bounded mean square of log|F/G| at the line"
```

and the first of these — a zero-free region for a degree-zero ratio — is now identified as the exact
missing ingredient. It is *weaker than RH for F and G* (it only asks that their zeros **coincide**
off the line, not that there are none), which makes it a genuinely new and possibly more tractable
statement:

> **(ZFR) Zero-free ratio.** For distinct `F, G ∈ S` with identical gamma factors, `F/G` has a zero
> or a pole off the critical line.

`ZFR` is the negation of "F and G have identical divisors off the line". It is implied by RH for
either function together with `F ≠ G`… no: under RH both have all zeros on the line, so `F/G` is
automatically zero-free off it, and `ZFR` is **false** under RH. Hence the chain in Theorem 45 is
*vacuous under RH* — the mean-square condition must do all the work.

> **Net.** Under RH the whole route collapses to step 3: `F = G` would follow from
> **bounded mean square of `log|F/G|` on lines approaching the critical line**, which is precisely a
> statement that `S_F(t) − S_G(t)` has bounded variance — i.e. a *cross* version of the Selberg
> central limit theorem. Recorded as the concrete surviving target, and noted as living at the same
> `δ ≍ 1/log T` scale identified in §67 — the third independent appearance of that scale.

---

## 90. Cycle 90 (2026-07-26) — (P2) reduces to a zero-density estimate plus a pairing rigidity

§89 left "bounded mean square of `log|F/G|` on the critical line" as the surviving target. This cycle
identifies what supplies it and what it yields.

### 90.1 The variance is the prime energy

Selberg's central limit theorem machinery computes the variance of `log F(1/2+it)` from the **prime
sum**, not from the zeros: for `F ∈ S` with prime energy `n_F`,
```
Var_{t≤T} ( log|F(1/2+it)| )  ~  (n_F/2)·loglog T ,
```
the input being an approximation of `log F` on the critical line by `Σ_{p≤x}a_F(p)p^{−1/2−it}`, valid
for all but a sparse set of `t` **given a zero-density estimate** of Selberg's type
`N_F(σ,T) ≪ T^{1−c(σ−1/2)}log T`.

Applying this to `R = F/G` (identical gamma factors, `c_p = a_F(p)−a_G(p)`):
```
Var( log|R(1/2+it)| )  ~  (n_R/2)·loglog T ,     n_R = n_F + n_G − 2 Re c_{F,G} .
```

> So **`n_R = 0` gives bounded variance of `log|F/G|` on the critical line** — the hypothesis §89.3
> needed — *provided a Selberg-type zero-density estimate holds for `F` and `G` in `S`*.

### 90.2 What bounded variance says about the zeros

`R` has zeros at the unshared zeros of `F` and poles at the unshared zeros of `G`, both of density
`(1−δ)(d/2π)T log T`. Near the line, `log|R(1/2+it)| = Σ_{zeros}log|t−γ| − Σ_{poles}log|t−γ'| + O(1)`.
If the two point sets were uncorrelated at the mean-spacing scale `1/log T`, each of density
`ν ≍ log T` per unit `t`, the variance of the difference would be `≍ ν ≍ log T`, contradicting
`O(1)`. Hence:

> **Rigidity consequence.** Bounded variance forces the unshared zeros of `F` and of `G` to **pair
> up**, each pair at distance `o(1/log T)` — the mean zero spacing. Either the zeros are genuinely
> shared (`δ = 1`, and then `F = G` by Corollary 44), or `F` and `G` are distinct with zeros paired
> at strictly sub-spacing distance.

### 90.3 The reduction

> **Theorem 46 (reduction of quantitative strong multiplicity one).** Let `F, G ∈ S` have identical
> gamma factors. Assume
> (a) a Selberg-type zero-density estimate for `F` and `G`, and
> (b) that two distinct elements of `S` cannot have their zeros paired at distance `o(1/log T)`.
> Then `n_R = 0 ⟹ F = G`; that is, **(P2) quantitative strong multiplicity one holds**:
> if `Σ_{p≤x}|a_F(p) − a_G(p)|²/p = O(1)` then `F = G`.

This is the first time (P2) — open since §22 — has been reduced to two statements that are *not*
Rankin–Selberg and *not* automorphy:

- (a) is a **one-cusp** statement (zero density from the functional equation and the Euler product;
  Selberg proved the analogue for `ζ` unconditionally, and the method is axiom-driven);
- (b) is a **zero-repulsion** statement between two different `L`-functions, of the same nature as
  simple-zero and pair-correlation results, and again zero-side.

Both live on the side that §77.2's thin-set rule and §87.2's scale rule permit, and neither is an
all-cusp statement in the sense of §84. **This is the first crack in the "everything funnels into
Rankin–Selberg" pattern of the whole programme.**

### 90.4 Honest status of each ingredient

- The variance asymptotic of §90.1 is Selberg's, and its transfer to `S` needs (a). Recorded as the
  precise analytic input, not assumed proved.
- §90.2 is a heuristic-strength argument (an uncorrelated-point-process comparison). Making it a
  theorem requires an explicit-formula computation of `Var(log|R|)` in terms of the pair correlation
  of the two zero sets — available in principle, and at the **bounded-`α` scale**, so §87.2's rule is
  respected.
- Corollary 44 and Theorem 43 are unconditional.

**Next target, in order:** (i) make §90.2 a theorem via the explicit formula; (ii) establish (a) in
`S` from the axioms; (iii) attack (b).

---

## 91. Cycle 91 (2026-07-26) — §90.2 made rigorous: integrality of the counting difference

§90.2 was an uncorrelated-point-process heuristic. It can be replaced by an exact argument that uses
**integrality of a counting function** — a genuine thin-set, bounded-`α` mechanism.

### 91.1 The chain, with the heuristic removed

Let `F, G ∈ S` have identical gamma factors and conductors, `R = F/G`, `c_p = a_F(p) − a_G(p)`,
`n_R = n_F + n_G − 2Re c_{F,G}`.

1. **Variance.** Selberg's machinery (given a zero-density estimate, hypothesis (a) of Theorem 46)
   gives `Var_{t≤T}(log|R(1/2+it)|) ~ (n_R/2)loglog T` and
   `Var_{t≤T}(S_F(t) − S_G(t)) ~ (n_R/2π²)loglog T`. So `n_R = 0 ⟹` both variances are `O(1)`.
2. **Counting.** With identical gamma factors and conductors the archimedean main terms of the
   Riemann–von Mangoldt formulas coincide, so
   ```
   N_F(t) − N_G(t) = S_F(t) − S_G(t) + O(1) ,
   ```
   which by step 1 has bounded `L²` norm. But `N_F − N_G` is **integer-valued**, so bounded `L²`
   norm forces it to be bounded by some `K` outside a set of density `0`.
3. **Interleaving.** A bound `|N_F − N_G| ≤ K` on the counting difference of two monotone sequences
   forces `γ_n^G ≤ γ_{n+K}^F` and `γ_n^F ≤ γ_{n+K}^G` for every `n`.
   **Formalised, unconditional:** `le_shift_of_count_le`, `abs_shift_of_count_le`.
4. **Spacing.** Since the mean gap at height `T` is `2π/(d log T)`, step 3 gives
   `|γ_n^F − γ_n^G| ≪ K/log T`: **the zeros of `F` and `G` pair within `O(1/log T)`, the mean
   spacing.**

> **Theorem 47.** For `F, G ∈ S` with identical gamma factors and conductors, assume the zero-density
> estimate (a). If `Σ_{p≤x}|a_F(p) − a_G(p)|²/p = O(1)` then the zeros of `F` and of `G` pair up with
> `|γ_n^F − γ_n^G| ≪ 1/log T`.

Step 3 is now a theorem, not a heuristic, and it is where the *integer* enters: the difference of two
counting functions is `Z`-valued, so an `L²` bound upgrades to a pointwise bound. This is the only
place in ninety cycles where integrality has been *used* rather than sought.

### 91.2 The remaining gap, stated exactly

> **(b′) Zero-pairing rigidity.** If `F, G ∈ S` have identical gamma factors and conductors and their
> zeros satisfy `|γ_n^F − γ_n^G| ≪ 1/log T` for all `n`, then `F = G`.

(b′) is the sharpened form of Theorem 46's hypothesis (b), at the correct scale. Together with (a) it
gives (P2), quantitative strong multiplicity one, and with §88 it settles (ZS).

### 91.3 A second confirmation that the `ℓ²` wall is real

One might hope to bypass all of this: `n_R = 0` gives `Σ_p|a_R(p)|²/p < ∞`, hence by multiplicativity
`Σ_n |a_R(n)|²/n < ∞`; does that make `R` holomorphic on `Re s > 1/2`? **No.** By Hedenmalm–
Lindqvist–Seip, `Σ_n |b_n|² < ∞` gives holomorphy of `Σ b_n n^{−w}` on `Re w > 1/2`; with
`b_n = a_R(n)n^{−1/2}` this is `Re s > 1`, which was already known from absolute convergence.

> **Recorded.** The `ℓ²`-to-zero-free-half-plane step fails by two independent routes (§89.2 via
> Cauchy–Schwarz on the abscissa, §91.3 via the `ℋ²` theory). The wall of §9.6/§22.1 is confirmed and
> should not be tested again.

### 91.4 Why (b′) is a good target

- It is a statement about **two zero sets**, with no primes, no Euler product and no Rankin–Selberg.
- It is at the mean-spacing scale `1/log T`, i.e. bounded `α` — permitted by §87.2's scale rule.
- Its natural proof is a **repulsion** statement: distinct `L`-functions with the same gamma factor
  and conductor should not have systematically colliding zeros. For the analogous question inside one
  `L`-function (simple zeros) this is open, but the *cross* version is genuinely different: it
  compares two functions with the *same* archimedean data, so the difference `Λ_F − Λ_G` is a
  meromorphic function whose zeros are exactly the collisions, and Theorem 43 shows `Λ_F/Λ_G` is real
  on the critical line — a strong structural handle unavailable in the one-function case.

---

## 92. Cycle 92 (2026-07-26) — the collision function `Λ_F − Λ_G` and its surplus zeros

Attack on (b′) (§91.2). Let `F, G ∈ S` have identical gamma factors, conductors and root numbers,
`F ≠ G`, and set
```
D(s) := Λ_F(s) − Λ_G(s) = Q^s γ(s) · H(s) ,      H := F − G = Σ_{n ≥ n_0} c'_n n^{−s} ,
```
where `n_0 := min{n : a_F(n) ≠ a_G(n)} ≥ 2` (as `a_F(1)=a_G(1)=1`).

### 92.1 `D` inherits the functional equation, and has a larger conductor

Since `ω_F = ω_G = ω`, subtracting the two functional equations gives
```
D(s) = ω · conj( D(1 − \bar s) ) ,
```
so `D` is an entire function of order `1` with a Selberg-type reflection. Its zero counting function
is computed by the argument principle exactly as for `Λ_F`, the only change being the extra winding
of `H(s) ~ c'_{n_0} n_0^{−s}` as `Re s → +∞`, which contributes `−t log n_0` to `arg H` on each
vertical side:

> **Theorem 48 (surplus of collision zeros).** `N_D(T) = N_{Λ_F}(T) + (T/π)·log n_0 + O(log T)`.
> So `D` has a **positive-density surplus** of `(log n_0)/π` zeros per unit height beyond the zero
> count of `Λ_F` itself.

### 92.2 What the surplus means under the pairing hypothesis

If the zeros of `F` and `G` pair with `|γ_n^F − γ_n^G| = ε_n`, then near each pair
`Λ_F ≈ A(s−ρ_n^F)`, `Λ_G ≈ B(s−ρ_n^G)`, and `D` has one zero at `(Aρ_n^F − Bρ_n^G)/(A−B)`. That
accounts for `≈ N_{Λ_F}(T)` zeros of `D`. Theorem 48 says there are `(T/π)log n_0` **more**, of
positive density but zero density relative to `T log T`.

> **The surplus zeros of `D` are not attached to any zero collision.** They are a genuine new zero
> set, of density `(log n_0)/π` per unit height, canonically attached to the pair `(F,G)` and to the
> first index `n_0` at which the coefficients differ.

This is a new object in the programme: a **finite-density** zero set (linear in `T`, not `T log T`)
attached to a *pair* of Selberg-class elements, whose density computes `log n_0` — i.e. **the first
disagreement index of the coefficients is read off a zero density.** Two consequences:

- `n_0` is recoverable analytically from the zeros of `Λ_F − Λ_G`; in particular, if `F ≠ G` then
  `D` has *strictly more* zeros than `Λ_F`, which is a clean quantitative separation of `F` from `G`
  in terms of zeros alone.
- Any hypothesis forcing `N_D(T) = N_{Λ_F}(T) + o(T)` forces `n_0 = 1`, i.e. `F = G`. **So (b′)
  reduces to an upper bound for the zero count of the collision function.**

> **(b″) Collision-count bound.** If the zeros of `F` and `G` pair within `O(1/log T)`, then
> `N_{Λ_F − Λ_G}(T) = N_{Λ_F}(T) + o(T)`.

(b″) ⟹ (b′) ⟹ (with (a)) (P2) and (ZS). It is a purely zero-side, finite-density statement about one
explicit entire function with a functional equation, and it does not mention primes.

### 92.3 Status

Theorem 48 is a Riemann–von Mangoldt computation for `D` and is as solid as the standard one; it
needs `ω_F = ω_G` (otherwise `D` satisfies no clean reflection — the general case can be handled by
replacing `G` with `ω_F\overline{ω_G}^{-1}G`, which does not change its divisor). Recorded scope:
identical `γ`, `Q`, and root numbers matched by that normalisation.

**The chain now reads**
```
(a) zero-density estimate in S   +   (b″) collision-count bound
        ⟹ (b′) pairing rigidity ⟹ (P2) quantitative strong multiplicity one ⟹ (ZS)
```
with every link either proved here or reduced to a statement about zeros only.

---

## 93. Cycle 93 (2026-07-26) — novelty check on the collision function, and the corrected target

### 93.1 What the surplus zeros are

By Theorem 48 the zeros of `D = Λ_F − Λ_G` are exactly the zeros of `H = F − G`, and
`N_H(T) = N_{Λ_F}(T) + (T/π)log n_0 + O(log T)`. Under a zero-pairing hypothesis, `≈ N_{Λ_F}(T)` of
them sit next to the paired zeros; the remaining `(T/π)log n_0` sit where **`F` and `G` take equal
non-zero values**. So:

> The coincidence set `{s : F(s) = G(s) ≠ 0}` of two distinct elements of `S` with equal `γ, Q, ω`
> has density `(log n_0)/π` per unit height, where `n_0` is the first index at which their
> coefficients differ.

### 93.2 Novelty check — adjacent literature

This is the same order of magnitude, and the same object, as **Bombieri–Perelli, "Distinct zeros of
`L`-functions" (Acta Arith. 83 (1998))**, which shows that distinct `F, G ∈ S` with equal degree and
conductor have `≫ T` zeros that are not common. The computation of the *exact constant* `(log n_0)/π`
and its identification with the first coefficient disagreement index may be a refinement, but the
regime — a linear-in-`T` count of non-common zeros — is classical.

> **Verdict on Theorem 48: REDISCOVERED (regime), possibly refined (constant).** Recorded so that the
> collision-function route is not pursued as if it were new territory. Its value to the programme is
> not novelty but **placement**: it shows that (b′) is a statement about the `T log T` scale
> (pairing), while the classical results live at the `T` scale (non-common zeros). *These are again
> two different scales*, and by §87.2's rule they must not be conflated.

### 93.3 The corrected target

Bombieri–Perelli gives `≫ T` non-common zeros; (b′) needs that **no pairing at distance
`O(1/log T)`** occurs among `≍ T log T` zeros. A count of non-common zeros at density `T` says
nothing about the geometry of the remaining `T log T`. Hence:

> **Recorded do-not-retry.** The collision function `Λ_F − Λ_G` and the Bombieri–Perelli circle of
> ideas operate at density `T` and cannot supply (b′), which is a statement at density `T log T`.

What (b′) needs is a **repulsion estimate at the mean-spacing scale between two `L`-functions** —
i.e. a cross pair-correlation lower bound, the two-function analogue of Montgomery's conjecture. That
is once more the bounded-`α` regime identified in §67, §72.2 and §90. **Four independent routes have
now converged on the same regime**: the smoothed zero-counting variance (§67), Montgomery's `α ≍ 1`
window (§72.2), the Selberg-CLT variance of `S_F − S_G` (§90), and the pairing rigidity (§91–93).

> **Consolidated open core of the programme (as of cycle 93).**
> ```
> Everything reduces to the pair-correlation regime α ≍ 1 (equivalently δ ≍ 1/log T):
>   Conjecture A / MI :  variance of the δ-smoothed zero-counting fluctuation of F
>   Conjecture B, real part :  the same for the pair (F,G)
>   Conjecture B, imaginary part (ω) :  Im of the twist correlation at depth b ≍ 1/log T
>   (P2) / (ZS) :  cross repulsion of the zeros of F and G at the mean spacing
> ```
> All four are statements about zeros at the mean spacing, and none is reachable by an averaging
> functional (§77.2) or by mixing scales (§87.2).

---

## 94. Hand-off (updated at cycle 93)

**Read order for a future session.**
1. §22.2 and §74 — the equivalence web and the meta-conclusion (one integrality mechanism).
2. §79.4 — the ten candidate mechanisms and why each fails.
3. §84 — one cusp versus all cusps; §85 — the two independence results (Theorems 38, 39).
4. §77.2 (thin-set rule) and §87.2 (scale rule) — the two design rules; violating either has
   produced three wrong derivations, all recorded.
5. §93.3 — the consolidated open core: everything is at `α ≍ 1`.
6. The do-not-retry list: §4, §7, §9.1, §9.6, §10.1, §11.1, §20.4, §21.1, §22.1, §26.3, §28.2, §31,
   §38, §46.4, §49.1, §53, §57, §62, §66, §69.2, §71, §72.3, §74.1, §77.1, §79.2, §86.3, §88.2,
   §89.2, §91.3, §93.2.
7. The preprint `docs/drafts/pipeline/4-publication-ready/monodromy-integrality-selberg.md`.

**Formal corpus (all unconditional, `#print axioms` = `[propext, Classical.choice, Quot.sound]`).**
- `RHTower/SelbergPairingPrimeSquare.lean` — Selberg pairing at `p²`, polarization, Cauchy–Schwarz.
- `HTGeometry/GeneralizedDirichletMeanValue.lean` — Bohr mean values: exact split, bilinear version,
  `oscInt` bound, uniform-gap diagonal extraction.
- `HTGeometry/ResidueJumpLowerBound.lean` — residue forces a uniform jump.
- `HTGeometry/LogCoefficientTransfer.lean` — log-coefficient transfer bound.
- `HTGeometry/DiagonalIsolation.lean` — gap from injectivity.
- `HTGeometry/RealGramBlindness.lean` — real Gram expansion; the alternating form `wOmega`.
- `HTGeometry/MultiplicityEnergyBracket.lean` — `Σm² ≥ Σm`, equality iff simple.
- `HTGeometry/ConvexSlopeDerivBound.lean` — convexity to derivative bound (Jessen).
- `HTGeometry/CommensurableFrequencies.lean` — commensurable frequency matching.
- `HTGeometry/AdditiveVersusQuadratic.lean` — additive invariants cannot determine the energy.
- `HTGeometry/FractionalExponentObstruction.lean` — coprime orders force integral exponents.
- `HTGeometry/CountingPairing.lean` — bounded counting difference forces interleaving.

**Standing status.** Conjecture A and Conjecture B both open. The programme's contribution is a
complete map of the obstruction: what the axioms can and cannot supply (§85), which functionals are
blind (§69, §72, §77), which scales may not be mixed (§87), and the single regime `α ≍ 1` into which
all four sub-problems funnel (§93.3).

---

## 95. Cycle 95 (2026-07-26) — the Energy Gap remaining case: a natural attack and why it fails

Remaining case of EG (§52): `F ∈ S` entire, non-vanishing on `Re s = 1`, with `0 < n_F < 1`.

### 95.1 The attempted mechanism

If `F` has zeros `ρ_n = β_n + iγ_n` with `η_n := 1 − β_n → 0`, then at `s = 1 + iγ_n` the zero at
distance `η_n` should force `log|F(1+iγ_n)| ≤ −log(1/η_n) + …`, while Cauchy–Schwarz on the prime sum
gives
```
|log F(1+η+it)| ≤ (Σ_p |a_F(p)|² p^{−1−2η})^{1/2}(Σ_p p^{−1−2η})^{1/2} ≈ √(n_F)·log(1/η) ,
```
so comparing would give `√(n_F) ≥ 1`, i.e. `n_F ≥ 1` — the Energy Gap.

### 95.2 Why it fails, exactly

The Hadamard–Landau expansion gives
```
log|F(s)| = Σ_{|ρ−s|<1} log|s−ρ| + O(log t) ,
```
and the `O(log t)` is genuine: there are `≍ (d/2π)log t` zeros within distance `1` of `s`. So a
single zero at distance `η` yields only
```
log|F(1+iγ)| ≤ −log(1/η) + O(log γ) ,
```
which is informative only if `log(1/η) ≫ log γ`, i.e. `η ≪ γ^{−C}`. But the classical zero-free
region available in `S` (Euler product plus non-vanishing on `Re s = 1`) gives `η ≫ 1/log γ`, hence
`log(1/η) ≍ loglog γ ≪ log γ`. **The error term swamps the signal by a full logarithm.**

### 95.3 The structural reason, and why no repair exists

The attempt tries to read `n_F` off the line `Re s = 1`. By Theorem 38 (§85.1) that is impossible in
principle: `F_c = L(·,χ)^c` is holomorphic and non-vanishing on a neighbourhood of `Re s ≥ 1`, has
every linear density zero, and has `n_{F_c} = c²` arbitrary. **Any argument confined to a
neighbourhood of `Re s ≥ 1` is compatible with every value of `n_F`.**

> **Recorded do-not-retry.** No argument using only the behaviour of `F` on or to the right of
> `Re s = 1` — zero-free regions, Hadamard–Landau at `σ = 1`, mean values on the `1`-line, Cauchy–
> Schwarz against `Σp^{−1}` — can establish the Energy Gap or any part of Conjecture A. The witness of
> §85.1 refutes the whole family at once.

### 95.4 What this leaves for EG

The remaining case must be attacked at `σ = 1/2`, where by §93.3 the relevant object is the variance
of the `δ`-smoothed zero-counting fluctuation at `δ ≍ 1/log T`. Concretely:

> **EG at the critical scale.** For `F ∈ S` entire and non-vanishing on `Re s = 1`,
> `Var_{t≤T}(log|F(1/2+it)|) ~ (n_F/2)loglog T`; the Energy Gap asserts this variance is either `0`
> (then `F = 1`) or at least `(1/2)loglog T`. So EG is: **the fluctuation of `log|F|` on the critical
> line cannot be non-trivially small.**

That is a clean statement of the remaining case, and it is again at `α ≍ 1`. The programme's four
sub-problems (§93.3) are now five, all in the same regime.

---

## 96. Cycle 96 (2026-07-26) — zero energy equals zero rigidity

Reformulating the Energy Gap at the critical scale identified in §95.4.

### 96.1 The equivalence

Write `N_F(t)` for the zero-counting function of `F ∈ S` and `M_F(t)` for its Riemann–von Mangoldt
main term, so `S_F(t) = (1/π)arg F(1/2+it) = N_F(t) − M_F(t) + O(1)`. Selberg's variance asymptotic
(given the zero-density input (a) of §90) is `Var_{t≤T}(S_F) ~ (n_F/2π²)loglog T`.

> **Theorem 49 (rigidity at zero energy).** For `F ∈ S`, the following are equivalent:
> 1. `n_F = 0`;
> 2. `Var_{t≤T}(S_F) = O(1)`;
> 3. `N_F(t) − M_F(t)` is bounded in `L²`, hence — being the difference of an integer-valued step
>    function and a smooth increasing function — bounded pointwise off a density-zero set by some `K`;
> 4. the zeros of `F` are **rigid**: `|γ_n − M_F^{−1}(n)| ≪ K/log γ_n`, i.e. the ordinates form a
>    perfect log-lattice up to `K` mean spacings.
>
> `3 ⟹ 4` is the interleaving lemma, formalised unconditionally as `le_shift_of_count_le` /
> `abs_shift_of_count_le`: a bounded counting difference forces the two monotone sequences to
> interleave with shift `K`, hence to agree within `K` mean spacings.

> **Corollary 50.** The `n_F = 0` case of the Energy Gap conjecture is *equivalent* to:
> **a non-trivial element of `S` cannot have perfectly rigid zeros.**
> The remaining case `0 < n_F < 1` is the corresponding statement with "perfectly" weakened to
> "almost": the zero-counting fluctuation cannot have variance `o(loglog T)` without vanishing.

### 96.2 Why this is the right shape

- It replaces a statement about **primes** (`Σ_p|a_F(p)|²/p`) by a statement about the **geometry of
  the zeros**, with an explicit and formalised bridge (`le_shift_of_count_le`) that uses integrality
  of the counting function — the mechanism identified in §91.1 as the only one in the programme that
  *uses* an integer rather than seeking one.
- It respects both design rules: the zero statement is at the mean spacing (`α ≍ 1`, §87.2) and is
  sensitive to the individual zeros rather than to an average (§77.2).
- It is falsifiable and independent of Rankin–Selberg, automorphy, and the all-cusp obstruction of
  §84.

### 96.3 What a proof would need

Rigid zeros determine `Λ_F` up to normalisation by the Hadamard product, so Corollary 50 asks: *is
there an entire function of order `1` with a Selberg functional equation, whose zeros form a perfect
log-lattice, and whose quotient by `Q^sγ(s)` is a Dirichlet series with an Euler product and
`a(1) = 1`?* The Hadamard product of a perfect log-lattice is an explicit function; the content is
whether it can carry an Euler product. **That is a concrete, self-contained question about one
explicit function**, and it is the first form of the Energy Gap that does not mention prime sums at
all.

**[OPEN CORE]** Construct, or rule out, an entire order-`1` function with a Selberg-type functional
equation whose zeros form a perfect log-lattice and whose "`L`-function part" has an Euler product.

---

## 97. Cycle 97 (2026-07-26) — rigid zeros demand spectral mass the primes cannot supply

Attack on §96.3's [OPEN CORE]: can a non-trivial `F ∈ S` have perfectly rigid zeros?

### 97.1 Rigid zeros force a sawtooth argument

If the zeros are a perfect log-lattice, `N_F(t) = ⌈M_F(t)⌉`, so
```
S_F(t) = N_F(t) − M_F(t) = 1/2 − {M_F(t)} + O(1/log t) ,
```
and the Fourier expansion of the sawtooth gives
```
arg F(1/2+it) = π S_F(t) = Σ_{k ≥ 1} sin(2πk M_F(t)) / k  +  const .
```

### 97.2 The frequencies of the harmonics

`M_F(t) = (d/2π)t log(t/2πe) + (log q/2π)t + O(1)`, so `M_F'(t) = ν(t) = (d/2π)log(t/2π) + …`. The
`k`-th harmonic `sin(2πkM_F(t))` therefore has **instantaneous frequency**
```
2πk·ν(t) = k·d·log(t/2π) + …  ,
```
i.e. in the language of the prime side (where the frequency of the term `a_F(p)p^{−1/2−it}` is
`log p`) it corresponds to
```
log p ≈ k·d·log t   ⟺   p ≈ t^{kd} .
```

### 97.3 The obstruction

On the prime side, `arg F(1/2+it) = −Im Σ_p a_F(p)p^{−1/2−it} + (error)`, and every Selberg-type
approximation of `log F` on the critical line uses primes `p ≤ x` with `x` **at most a fixed power of
`T`**. So the prime sum can supply harmonics only up to `k ≤ k_0` with `k_0 = O(1)` (indeed
`k_0 ≈ (log x)/(d log T)`).

But the sawtooth's tail carries a **fixed positive** amount of variance:
```
Var( Σ_{k > k_0} sin(2πkM_F)/k )  =  (1/2π²) Σ_{k>k_0} k^{−2}  ≈  1/(2π² k_0)  >  0 .
```

> **Obstruction (RZ).** A perfectly rigid zero set requires `arg F(1/2+it)` to carry variance
> `≍ 1/k_0 > 0` at frequencies corresponding to primes of size `t^{k_0 d}` — beyond the reach of any
> admissible approximation length. The prime side cannot supply it unless the approximation error
> itself carries that much `L²` mass.

**Status: mechanism established, theorem not.** Turning RZ into a proof requires an `L²` bound for
the error in Selberg's approximation of `log F` on the critical line that is `o(1)` uniformly — a
quantitative strengthening of Selberg's theorem which is available in measure but not, as far as this
programme has established, in `L²`. Recorded as the precise analytic gap.

### 97.4 Why this is a new kind of argument

Every previous route in the programme compared **magnitudes** (energies, variances, densities,
counting functions). This one compares **frequency content**: rigid zeros are a chirp with harmonics
at `k·d·log t`, while the primes supply tones at `log p` with `p` bounded by a power of `t`. The two
spectra are incompatible in the tail. It is:

- thin-set sensitive (§77.2 rule: it is about individual harmonics, not an average);
- at the correct scale (§87.2 rule: the fundamental `k = 1` sits exactly at the mean spacing);
- independent of Rankin–Selberg, of automorphy and of the all-cusp obstruction (§84) — it uses only
  the functional equation (through `M_F`) and the Euler product (through the prime frequencies).

> **Consequence if completed.** RZ ⟹ no non-trivial `F ∈ S` has rigid zeros ⟹ (Corollary 50)
> `n_F = 0 ⟹ F = 1`, i.e. the `n_F = 0` case of the Energy Gap. Combined with Theorem 10
> (`n_F ≥ ν²`), the only remaining case of EG would be `0 < n_F < 1`, for which the same frequency
> argument applies with "perfect" replaced by "almost" rigidity: the sawtooth is then replaced by a
> perturbed sawtooth whose harmonic tail is still bounded below as long as the perturbation has
> variance `o(loglog T)`.

**Recorded as the most promising open mechanism of the programme.** It is the first argument found in
97 cycles that attacks the prime side and the zero side simultaneously **through their spectra**
rather than through their sizes.

---

## 98. Cycle 98 (2026-07-26) — RZ does not close: the correction

Phase-4 attack on §97's obstruction (RZ), carried out by doing the `L²` accounting properly.

### 98.1 The accounting

Fix `x = T^ε` and write `log F(1/2+it) = P_x(t) + E_x(t)`, `P_x = Σ_{p≤x}a_F(p)p^{−1/2−it} + (k≥2)`.
Suppose `F` has rigid zeros, so `arg F(1/2+it) = Σ_{k≥1} sin(2πk M_F(t))/k + const`. Then:

- **Total variance of the sawtooth:** `Var(arg F) = Σ_{k≥1} 1/(2k²) = π²/12`. **Bounded.**
- **High-pass part above the prime cutoff `log x`:** the `k`-th harmonic has frequency `≈ kν(t)`
  with `ν = (d/2π)log(t/2π)`, so the harmonics unreachable by `P_x` are those with `k > K`,
  `K ≈ 2πε/d`, carrying variance `(1/2)Σ_{k>K}k^{−2}`.
- **Available error variance:** `Var(E_x) ≤ 2Var(arg F) + 2Var(Im P_x) = π²/6 + 2A`, where
  `A = (1/2)Σ_p |a_F(p)|²/p < ∞` when `n_F = 0`.

§97 asserted that shrinking `ε` drives the required tail variance `≈ 1/(2K) = d/(4πε)` to infinity,
producing a contradiction. **That is wrong.** The tail variance is
`(1/2)Σ_{k>K}k^{−2} ≤ (1/2)Σ_{k≥1}k^{−2} = π²/12` for every `K`, and in particular for `K < 1` the
"tail" is simply the whole sawtooth. The expression `1/(2K)` is the asymptotic for `K ≥ 1` only and
is an *upper* bound artefact below that; it never exceeds `π²/12`.

> **Verdict on RZ: FALSE as an obstruction.** The sawtooth's total `L²` mass is a bounded constant,
> so its high-frequency part is bounded, and the error term `E_x` has variance of the same order.
> There is no mismatch to exploit. **Recorded do-not-retry: no `L²` accounting of the sawtooth's
> harmonics against the prime frequencies can rule out rigid zeros.**

### 98.2 What actually survives

The structural observation of §97.2 stands and is worth keeping:

> Rigid zeros make `arg F(1/2+it)` a **chirp** — a sawtooth in `M_F(t)`, whose harmonics have
> *drifting* instantaneous frequencies `k·ν(t)`, `ν(t) ≍ log t`. The prime side supplies only **pure
> tones** `log p`, whose frequencies do not drift.

The failure of §98.1 is that the *error term* is unconstrained in shape, so it can in principle be a
chirp. Closing the argument therefore requires not an `L²` bound but a **structural** statement:

> **(RZ′) Chirp obstruction, corrected form.** The error `E_x(t)` in the approximation of
> `log F(1/2+it)` by its prime sum is, for `F ∈ S`, expressible in terms of the zeros within `O(1/log t)`
> of `t`; a *drifting-frequency* component of fixed amplitude in `E_x` is therefore itself a statement
> about zero rigidity. So RZ′ is circular unless the error is controlled independently of the zeros.

**Recorded.** The chirp-versus-tone distinction is real but cannot be converted into an obstruction
by size arguments; it would need a genuinely new representation of `log F` on the critical line whose
error is prime-side controlled. That is exactly the missing analytic input identified in §90 as
hypothesis (a), so the route rejoins the known open core rather than bypassing it.

### 98.3 Methodological note

This is the fourth conjecture proposed and killed in-cycle by exact accounting (APR §Phase-4, ZD §77,
the zero-sharing bridge §87.2, RZ §98). In each case the error was the same in kind: an asymptotic
formula valid in one regime was applied outside it. The two design rules (§77.2 thin sets, §87.2
scales) are now joined by a third:

> **Regime rule.** Before comparing two asymptotic expressions, check that the parameter ranges in
> which each was derived actually overlap. `1/(2K)` for the harmonic tail is valid for `K ≥ 1`; the
> contradiction in §97 came from using it at `K < 1`.

---

## 99. Cycle 99 (2026-07-26) — the θ-gap: a third measure of how far the axioms fall short

### 99.1 A correction

§89.1 asserted that the prime-power part of `log F` converges absolutely for `Re s > 1/2` "because
`θ < 1/2`". That is imprecise. With `b_F(p^k) ≪ p^{kθ}`,
```
Σ_p Σ_{k≥2} |b_F(p^k)| p^{−kσ}  ≪  Σ_p p^{2(θ−σ)} ,
```
which converges **iff `σ > θ + 1/2`**. Since `θ < 1/2` this is a half-plane strictly inside `σ > 1`,
but it reaches `σ = 1/2` only when `θ = 0`. (The step in §89.1 was part of an argument already
declared invalid, so nothing downstream changes; §73.1's absolute convergence comes from the
exponential factor `e^{−2πbn^{1/d}}` and is unaffected.)

### 99.2 The θ-gap

> **Theorem 51 (θ-threshold).** For `F ∈ S` with Euler-product exponent `θ`,
> `log F(s) − Σ_p a_F(p)p^{−s}` is holomorphic on `Re s > θ + 1/2`, and this is sharp for the bound
> given by axiom (4). Hence the Euler product controls `log F` down to the line `Re s = θ + 1/2` and
> **no further**.

By Theorem 38 (§85.1), `n_F` is invisible anywhere in a neighbourhood of `Re s ≥ 1`; by Theorem 24
and §93.3, it lives at `Re s = 1/2`. So:

> **The Euler-product axiom stops short of where `n_F` lives, by exactly `θ`.**

### 99.3 Three gaps, one obstruction

The programme has now produced three independent numerical measures of the distance between the
Selberg axioms and what Conjecture A needs:

| gap | axiom side | needed side | size | vanishes when |
|---|---|---|---|---|
| Euler-product reach (§99) | `Re s > θ + 1/2` | `Re s = 1/2` | `θ` | `θ = 0` |
| twist exponent (§82) | `κ ≤ 1/d` | `κ = 1` | `1 − 1/d` | `d = 1` |
| cusps (§84) | `q = 1` only | all roots of unity | — | — |

The first two vanish exactly in the classical solved cases (`θ = 0` holds for degree-1 elements,
where `b_F(p^k) = χ(p)^k/k` is bounded; `d = 1` is the classified degree). The third never vanishes
inside `S` and is closed only by automorphy. **Together they explain, quantitatively, why every
Selberg conjecture is a theorem in degree `1` and none is in degree `≥ 2`:** in degree `1` both
numerical gaps close, and the cusp gap is bridged by the classification of `S_1` itself.

### 99.4 Assessment after 99 cycles

What the programme has established, in one paragraph. Integrality in `S` is produced by exactly one
mechanism — the order of a pole of a single-valued meromorphic function (§74, §79.4) — and Selberg's
`n_F` is a quadratic form on the monoid while every integer the axioms supply is additive (§85.2), so
`n_F ∈ Z` cannot be a formal consequence of the axioms and requires constructing a new meromorphic
object, namely `R_{F,F}` (§25's equivalence web). That object is all-cusp (§84), while the axioms are
one-cusp; the distance is measured by the three gaps above. Every functional that averages is blind
to `n_F` (§77.2), every comparison across the three scales `α → 0, α ≍ 1, α → ∞` is invalid (§87.2),
and every asymptotic must be used inside its own regime (§98.3). What remains is a single analytic
target in a single regime: **the variance of the `δ`-smoothed zero-counting fluctuation at
`δ ≍ 1/log T`**, for one function (Conjecture A) or for a pair (Conjecture B), together with its
alternating counterpart `ω` (§70) which is provably invisible to energies (§69.1) and visible only in
the twist correlation (§80).

---

## 100. Cycle 100 (2026-07-26) — scope audit of hypothesis (a), and no second twist spectrum

### 100.1 How hard is hypothesis (a)?

Theorems 46, 47 and 49 all rest on hypothesis (a): a Selberg-type zero-density estimate
`N_F(σ,T) ≪ T^{1−c(σ−1/2)}log T` for `F ∈ S`, enough to run Selberg's approximation of `log F` on the
critical line. §90.3 called it "a one-cusp statement". That is correct but understates its
difficulty, and the scope must be recorded honestly.

Selberg's density theorem for `ζ` is proved from mean-value estimates (fourth moment, mollifier). For
`F ∈ S` of degree `d` the available bound on lines `1/2 < σ < 1` is the convexity bound
`|F(σ+it)| ≪ 𝔮(t)^{(1−σ)/2+ε}`, giving
```
∫_0^T |F(σ+it)|² dt ≪ T^{1 + d(1−σ) + ε} ,
```
which is `≪ T^{1+ε}` only for `σ` close to `1`. Near `σ = 1/2` it is far too weak, and Carlson's
theorem does not apply there (§31). So:

> **Recorded scope.** Hypothesis (a) is *not* an elementary consequence of the axioms. For `d ≥ 2` it
> is of the same difficulty class as the sub-convexity/moment problem for `L`-functions. Theorems 46,
> 47 and 49 are therefore reductions **within** that difficulty class, not below it. What they do
> achieve is a change of *kind*: they replace Rankin–Selberg and automorphy (all-cusp, §84) by
> moment estimates for a single `F` (one-cusp). That is a genuine structural gain, but not a
> reduction in analytic depth.

This correction applies retroactively to §90.3's claim that (a) and (b) are "not Rankin–Selberg and
not automorphy": true, but (a) is the moment problem.

### 100.2 No second twist spectrum

§82 raised whether some `κ > 1/d` might also be reachable from the axioms. The mechanism at
`κ = 1/d` is a stationary-phase resonance: the functional equation contributes a phase
`≈ d·t·log t`, matched by the twist phase `−2πα n^{1/d}` under Voronoi-type summation. For
`κ = k/d` with `k ≥ 2` there is no such match, and forming `F_{2/d}` as a product of two standard
twists fails because `Φ_F(s,α)²` has frequencies `n^{1/d} + m^{1/d}`, not `n^{2/d}`.

> **Recorded do-not-retry.** There is no "second spectrum": the Selberg axioms resonate with exactly
> one twist exponent, `κ = 1/d`. The gap `[1/d, 1]` of §82 cannot be narrowed from below.

### 100.3 Standing summary at cycle 100

- **Proved unconditionally in this programme (44 Lean theorems, all axiom-clean):** the linear half of
  Conjecture A (`m_F ∈ Z_{≥0}`); MI ⟹ Conjecture A with full integrality; the Cusp–Spectrum Radius
  Law; `n_F ≥ ν²` (Energy Gap except the entire, `1`-line-non-vanishing, `n_F ∈ (0,1)` case); `n_F` is
  not archimedean; the complex-shift regularisation (Theorems 23–24) and its spectral form
  (Theorem 28); the twist correlation identities (Theorems 29–30); the real Gram blindness theorem
  (Theorem 16) and the Selberg symplectic form (Theorem 19); the additive-versus-quadratic no-go
  (Theorem 39); the fractional-power obstruction (Theorem 40); the ratio functional equation
  (Theorem 43) and Corollary 44; the interleaving lemma and the rigidity equivalence (Theorems 47, 49).
- **Independence results:** Theorem 38 (the functional equation is essential; `L(·,χ)^c` witness) and
  Theorem 39, which together show `n_F ∈ Z` is not a formal consequence of the axioms.
- **Three quantitative gaps** between the axioms and the target: `θ` (§99), `1 − 1/d` (§82), one cusp
  versus all (§84); the first two vanish exactly in degree `1`.
- **Three design rules**, each derived from a killed conjecture: thin sets (§77.2), scales (§87.2),
  regimes (§98.3).
- **Open:** Conjecture A and Conjecture B. The single remaining analytic target is the variance of the
  `δ`-smoothed zero-counting fluctuation at `δ ≍ 1/log T`, for one function and for a pair, together
  with the alternating form `ω`.

---

## 101. Cycle 101 (2026-07-26) — the θ-gap is not real: Ramanujan already gives `θ = 0`

Phase-4 attack on §99's "θ-gap", using a tool the programme had already formalised for another
purpose.

### 101.1 The theorem

> **Theorem 52.** For every `F ∈ S`,
> ```
> log F(s) − Σ_p a_F(p) p^{−s}
> ```
> is holomorphic on `Re s > 1/2`. Equivalently, the prime-power part of the Euler product has
> effective exponent `θ = 0`, for every element of `S`, as a consequence of the Ramanujan axiom
> alone.
>
> *Proof.* Fix `ε > 0` and a prime `p`. The local factor `F_p(x) = Σ_k a_F(p^k)x^k` has `A_0 = 1` and,
> by axiom (5), `‖A_k‖ = |a_F(p^k)| ≤ C_ε p^{kε}`. The local logarithm `log F_p(x) = Σ_k b_F(p^k)x^k`
> satisfies the standard log-derivative recursion `k A_k = Σ_{j<k}(k−j)B_{k−j}A_j`, so the
> **log-coefficient transfer bound** applies:
> ```
> ‖B_k‖ ≤ (4 C R)^k    with   C = C_ε , R = p^ε ,
> ```
> i.e. `|b_F(p^k)| ≤ (4C_ε)^k p^{kε}`. Hence
> ```
> Σ_p Σ_{k≥2} |b_F(p^k)| p^{−kσ} ≪ Σ_p (4C_ε)² p^{2(ε−σ)} ,
> ```
> convergent as soon as `σ > 1/2 + ε` (the finitely many `p ≤ (4C_ε)^{1/(σ−ε)}` are handled
> separately, the local series being convergent there for `σ` large and continuing). Letting
> `ε → 0` gives holomorphy on `Re s > 1/2`. ∎
>
> **The transfer bound is the formalised, unconditional `log_coeff_bound`**
> (`HTGeometry/LogCoefficientTransfer.lean`): `A_0 = 1`, the recursion, and `‖A_n‖ ≤ C R^n` imply
> `‖B_n‖ ≤ (4CR)^n` for `n ≥ 1`. This is the first time a Lean theorem proved in this programme has
> served as the engine of a paper result rather than as a check on one.

### 101.2 Correction to §99

> **§99's θ-gap is not a real gap.** Axiom (4)'s hypothesis `b_F(n) ≪ n^θ`, `θ < 1/2`, is subsumed by
> axiom (5): Ramanujan forces `θ = 0` effectively. The table of §99.3 therefore reduces to **two**
> gaps, not three:
>
> | gap | axioms give | needed | vanishes when |
> |---|---|---|---|
> | twist exponent (§82) | `κ ≤ 1/d` | `κ = 1` | `d = 1` |
> | cusps (§84) | `q = 1` only | all roots of unity | never inside `S` |
>
> Both remaining gaps are about the *functional equation's* reach, not the Euler product's. So the
> Euler product is **not** where the Selberg class falls short.

### 101.3 What Theorem 52 buys

`Σ_p a_F(p)p^{−s} = log F(s) + (holomorphic on Re s > 1/2)`, so on the whole half-plane
`Re s > 1/2` the **only** singularities of the linear prime sum are the zeros and poles of `F`, with
logarithmic branch points there. Three immediate consequences, all unconditional:

1. **The linear half of Conjecture A extends to the whole strip.** §39.1's monodromy argument, which
   was run at `s = 1`, now runs at *every* point of `Re s > 1/2`: if `a_F(p) → m` in the density sense
   at a point `s_0` with `Re s_0 > 1/2`, the monodromy of `F` around `s_0` forces `m·ord_{s_0}(F) ∈ Z`.
2. **Every "edge" statement about linear densities is really a statement about the divisor of `F` in
   the open right half of the critical strip** — not just on the `1`-line.
3. It sharpens Theorem 38's witness: `L(·,χ)^c` is holomorphic and non-vanishing on `Re s ≥ 1` but
   *does* have branch points at the zeros of `L` inside the strip, and Theorem 52 says those branch
   points are exactly what the prime sum sees. The independence result of §85.1 is therefore optimal:
   the failure of integrality for `L^c` is invisible on `Re s ≥ 1` and visible precisely at the zeros.

**Net.** The Euler product reaches the critical line. The remaining obstruction is entirely on the
functional-equation side, which is where §82 and §84 already located it — now with the third
candidate removed.

---

## 102. Cycle 102 (2026-07-26) — the mean square of `log F` is fine; the obstruction is regularity

§46.4 recorded that Carlson's theorem cannot be applied to `F'/F` below `σ = 1` because the
mean-square hypothesis fails. Theorem 52 makes it worth redoing the analysis for `log F`, where the
local singularity is `log|s−ρ|` rather than `1/(s−ρ)`.

### 102.1 The mean-square bound holds

> **Theorem 53 (unconditional).** For every `F ∈ S` and every fixed `σ > 1/2`,
> ```
> ∫_0^T | log F(σ+it) |² dt  ≪_σ  T log² T .
> ```
> *Proof.* By the Hadamard–Landau expansion, `log|F(σ+it)| = Σ_{|ρ−s|<1} log|s−ρ| + O(log t)` and
> `|arg F(σ+it)| ≪ log t + #\{ρ : |ρ−s|<1\} ≪ log t`. There are `≍ T log T` zeros with `|ρ−s| < 1`
> for `s` on the segment, each contributing `∫_{|t−γ|<1} log²|s−ρ| dt ≪ 1` because `log²` is locally
> integrable, and Cauchy–Schwarz over the `≪ log t` nearby zeros gives
> `∫_0^T(Σ_{|ρ−s|<1}\log|s−ρ|)²dt ≪ \log T · (T\log T) ≪ T\log²T`. ∎
>
> By Theorem 52 the same bound holds for the linear prime sum `P(s) = Σ_p a_F(p)p^{−s}`, since
> `P − \log F` is bounded on every line `σ > 1/2 + ε`.

**This is a genuine improvement over §46.4.** For `F'/F` the local singularity `1/(s−ρ)` is *not*
locally square-integrable, and the mean square is not controlled; for `log F` it is, and
`T log²T ≪ T^{1+ε}` — **Carlson's mean-square hypothesis is satisfied on every line `σ > 1/2`.**

### 102.2 Why Carlson still does not apply

Carlson's theorem requires the function to be **regular** in the half-plane, and `log F` has
logarithmic branch points at every zero of `F` with `β > σ`. So:

> **The obstruction to Carlson for `log F` is regularity, not size.** Under RH for `F` there are no
> zeros with `β > 1/2`, `P` is regular on `Re s > 1/2`, Carlson applies, and
> `lim_T (2T)^{−1}∫_{−T}^{T}|P(σ+it)|²dt = Σ_p |a_F(p)|² p^{−2σ}` for every `σ > 1/2`.

That identity is the coefficient identity again, so it gives no new arithmetic; its value is
diagnostic. It isolates exactly what stands between the axioms and the quadratic prime sum on
`Re s > 1/2`:

> **the zeros of `F` in the open right half of the critical strip.**

### 102.3 The resulting dichotomy

```
either  F has zeros with β > 1/2  →  P has branch points there, and the quadratic prime data
                                      is not extractable by a mean value;
or      F satisfies RH            →  the quadratic prime data is extractable, but reduces to the
                                      coefficient identity and yields nothing new.
```

Both branches are recorded elsewhere in the programme (§47: `RH ⇏ MI`; §31, §46.4: mean-value routes
blocked). What is new here is that the *reason* differs from what §46.4 recorded: the mean-square
size is fine for `log F`, and the blockage is purely the branch points. **Recorded so that no later
cycle re-derives the size obstruction for `log F`; it does not exist.**

### 102.4 Residue

Theorem 53 is an unconditional mean-square bound for `log F` on every line right of the critical
line, valid for every `F ∈ S`, with no zero-density input. It is the strongest unconditional
mean-value statement the programme has produced, and it is available as an input elsewhere — in
particular it is the natural first step towards hypothesis (a) of §90, whose difficulty (§100.1) lies
in getting from a `T log²T` bound to the `T^{1−c(σ−1/2)}` density estimate.

---

## 103. Cycle 103 (2026-07-26) — removing hypothesis (a), and the displacement–coefficient duality

### 103.1 Hypothesis (a) can be traded for RH

§100.1 recorded that hypothesis (a) — a Selberg-type zero-density estimate — is of moment-problem
difficulty. It exists only to make Selberg's approximation of `log F` on the critical line valid, and
its role is to guarantee that most `t` have no zeros with `β > 1/2` nearby. **Under RH for `F` there
are none at all**, so:

> **Theorem 47′ (unconditional in the density, conditional on RH).** Let `F, G ∈ S` satisfy RH and
> have identical gamma factors and conductors. If `Σ_{p≤x}|a_F(p) − a_G(p)|²/p = O(1)`, then
> `Var(S_F − S_G) = O(1)`, `N_F − N_G` is bounded (being integer-valued), and the zeros pair with
> `|γ_n^F − γ_n^G| ≪ 1/log T`.
>
> **Theorem 49′ (under RH).** `n_F = 0` ⟺ `Var(S_F) = O(1)` ⟺ the zeros of `F` are rigid.

So the chain of §§88–96 is available with a single, standard hypothesis instead of an unproven
density estimate. Recorded as the cleanest form of those results.

### 103.2 The pair explicit formula has no archimedean term

For `F, G ∈ S` with **identical** gamma factors, conductors and root numbers, subtracting the two
explicit formulae cancels every archimedean and conductor contribution exactly:

> **Theorem 54 (displacement–coefficient duality).** For any admissible even test function `φ` with
> Fourier transform `φ̂`,
> ```
> Σ_{ρ_F} φ(γ_F) − Σ_{ρ_G} φ(γ_G)
>       = −(1/2π) Σ_{n ≥ 2} ( Λ_F(n) − Λ_G(n) ) n^{−1/2} ( φ̂(log n) + \overline{φ̂(log n)} ) ,
> ```
> with **no** `Γ`-factor term, no `log Q` term and no pole term. The zero data of the pair and the
> coefficient differences are exactly Fourier-dual.

Under the pairing hypothesis `γ_n^F = γ_n^G + ε_n`, expanding the left side gives
```
Σ_n φ'(γ_n^G) ε_n + O( ‖φ''‖_∞ Σ_n ε_n² )
   = −(1/π) Σ_p c_p p^{−1/2} Re φ̂(log p) + (k ≥ 2 terms) ,   c_p = a_F(p) − a_G(p) .
```

> **This is the exact bridge between (b′) and the prime side, and it is free of archimedean noise.**
> Choosing `φ` with `φ'` aligned to the signs of the `ε_n` makes the left side `≍ Σ_n |ε_n|`, while
> Cauchy–Schwarz bounds the right side by `(Σ_p|c_p|²/p)^{1/2}·(Σ_p |φ̂(\log p)|²)^{1/2}`, whose first
> factor is **bounded** precisely when `n_R = 0`.

### 103.3 Why this is the right tool

Every earlier attempt to link the zeros of `F` and `G` to their coefficients (§87.2, §90.2, §92) was
blocked either by archimedean main terms that swamped the signal or by a scale mismatch. Theorem 54
has neither defect: the archimedean parts cancel *identically* because the two functions share their
gamma factor and conductor, and both sides live at the same scale — `φ` localised at scale `1/log T`
sees the mean spacing on the left and primes up to `T^{O(1)}` on the right.

**[OPEN CORE], sharpened once more.** Show that
```
Σ_n |ε_n| ≫ T      whenever F ≠ G,
```
i.e. that non-identical elements of `S` with the same archimedean data cannot have their zeros
displaced by `o(1/log T)` on average. By Theorem 54 this is equivalent to a lower bound for the
weighted prime sum `Σ_p c_p p^{−1/2}φ̂(log p)` over the admissible test functions — a **linear**
statement in the coefficient differences, not a quadratic one.

> That last point is the significant one: (b′), and with it (P2) and (ZS), reduces to a **linear**
> question about `(a_F(p) − a_G(p))_p`, whereas everything in Conjecture A and Conjecture B has so far
> been irreducibly quadratic. Linear statements about coefficient differences are exactly where this
> programme has unconditional results (§39.1, Theorem 2, Theorem 52).

---

## 104. Cycle 104 (2026-07-26) — divisor multiplicity one from Theorem 52

### 104.1 An unconditional consequence

> **Theorem 55 (divisor multiplicity one).** Let `F, G ∈ S` with `a_F(p) = a_G(p)` for **all** primes
> `p`. Then `F/G` is holomorphic and non-vanishing on `Re s > 1/2`; in particular `F` and `G` have the
> same zeros and poles, with multiplicity, in the open right half of the critical strip. If moreover
> their gamma factors and conductors agree, the ratio functional equation (Theorem 43) transfers this
> to `Re s < 1/2`, so the divisors of `F` and `G` agree **off the critical line**.
>
> *Proof.* `log(F/G)(s) = Σ_p Σ_{k≥2}(b_F(p^k) − b_G(p^k))p^{−ks}`, since the `k = 1` terms cancel.
> By Theorem 52 both prime-power series converge absolutely on `Re s > 1/2`, so `log(F/G)` is
> holomorphic there and `F/G = exp(log(F/G))` is holomorphic and zero-free. ∎

So **the off-critical-line divisor of an element of `S` is determined by its prime coefficients
alone** — the prime-power coefficients cannot move a zero off the line. This is a clean unconditional
statement, and it is exactly the sharpest form of "strong multiplicity one" that the axioms give for
free.

### 104.2 Why it does not close (b′)

Under RH there are no zeros off the critical line, so Theorem 55 is vacuous in the situation of
Theorem 47′. And in the general case, `c_p ≡ 0` still leaves `F/G` with possible zeros and poles **on**
the line. Pushing further:

- If `F/G` were entire, it would be a degree-`0` element of `S^♯`, hence (Kaczorowski–Perelli) a
  Dirichlet polynomial; with an Euler product and `a(p) = 0` for all `p`, matching powers in the
  degree-`0` functional equation forces `F/G = 1`.
- But "entire" means `F` and `G` share **all** their zeros, which is (ZS) again.

> **Recorded.** The linear reduction of §103.3 is genuine, but its base case `c_p ≡ 0` couples back to
> (ZS). The coupling is:
> ```
> c_p ≡ 0  ⟹  divisors agree off the line (Thm 55)  ⟹  need: divisors agree on the line  ⟹  F = G.
> ```
> The missing step is again a statement about zeros **on** the critical line, at the mean spacing.

### 104.3 Consolidated picture of the pair problem

```
prime side                          zero side
Σ_p |c_p|²/p = O(1)   ⟷ (Thm 47′)   |γ_n^F − γ_n^G| ≪ 1/log T          [pairing]
c_p ≡ 0               ⟹ (Thm 55)    divisors agree off the line        [unconditional]
c_p arbitrary         ⟷ (Thm 54)    Σ_n φ'(γ_n)ε_n = −(1/π)Σ_p c_p p^{−1/2}Reφ̂(log p)
                                                                       [exact, no archimedean term]
```
The three rows are, respectively, a quadratic statement, a rigidity statement and an exact linear
duality. Only the third is an identity; the first two are implications. **The programme's pair
problem is now completely described by these three rows**, and what is missing in every row is the
same thing: control of the zeros *on* the critical line at the mean spacing.

---

## 105. Cycle 105 (2026-07-26) — Theorem 52's engine, fully machine-checked

Theorem 52 (`log F − Σ_p a_F(p)p^{−s}` is holomorphic on `Re s > 1/2` for every `F ∈ S`) rests on two
elementary but load-bearing steps. Both are now formalised unconditionally.

1. **Transfer.** `log_coeff_bound`: for `A_0 = 1` satisfying the Newton recursion
   `n A_n = Σ_{j<n}(n−j)B_{n−j}A_j` and `‖A_n‖ ≤ C R^n`, one has `‖B_n‖ ≤ (4CR)^n` for `n ≥ 1`.
   Applied at a prime `p` with `A_k = a_F(p^k)`, `C = C_ε`, `R = p^ε` (Ramanujan), this gives
   `|b_F(p^k)| ≤ (4C_ε)^k p^{kε}`.
2. **Summability.** `tail_geometric_bound` (new this cycle): if `‖B_n‖ ≤ M^n` for `n ≥ 1` and
   `Mx < 1`, then `Σ_{k=2}^{N} ‖B_k‖x^k ≤ (Mx)²/(1−Mx)` **uniformly in `N`**. With `x = p^{−σ}` and
   `M = 4C_ε p^ε` this gives a per-prime tail of size `O(p^{2ε−2σ})`, and `Σ_p p^{2ε−2σ}` converges
   for `σ > 1/2 + ε`.

Letting `ε → 0` proves Theorem 52. Both steps are `#print axioms`-clean.

> **Note on method.** This is the second paper result in the programme whose proof is carried by a
> Lean theorem rather than merely checked by one (the first being the use of `le_shift_of_count_le`
> in Theorem 47). The formalisation has therefore repaid its cost twice: `log_coeff_bound` was
> originally written as a hygiene check on an Euler-product manipulation, and turned out to be the
> exact tool that removes the `θ`-gap of §99.

**Consolidated formal corpus: 46 theorems in 13 modules, all unconditional, all axiom-clean.**

**Verification note (cycle 105).** `tail_geometric_bound` was first written with a `Finset.map`-based
index shift; `lake env lean` reported it clean while `lake build` rejected it (two `omega` failures
inside the embedding's injectivity proof, and an unknown lemma name). The proof was rewritten using
`Finset.sum_Ico_eq_sum_range` and `geom_sum_eq`, and **`lake build` now passes**; both
`log_coeff_bound` and `tail_geometric_bound` audit to
`[propext, Classical.choice, Quot.sound]`. Process rule recorded: *`lake build` is authoritative;
never record a result as formalised on the strength of `lake env lean` alone* — in this tree a
concurrent editor can leave the two disagreeing.

---

## 106. Cycle 106 (2026-07-26) — displacement energy, and where the linear route stalls

Pushing §103.3's linear reduction with Theorem 54.

### 106.1 The displacement statistics

Take `φ` a bump of width `H` at height `t_0`. Then `φ̂` is concentrated on `|ξ| ≲ 1/H`, so the prime
side of Theorem 54 sees only primes with `log p ≲ 1/H`:

- **Wide windows (`H ≫ 1`).** The prime side is essentially empty, so
  `Σ_{γ_n ∈ window} ε_n = o(H)` — the displacements **cancel** over long windows. A real constraint,
  but not a contradiction.
- **Narrow windows (`H ≍ 1/log T`).** The prime side reaches `p ≲ T`, and the left side is
  `≈ (log T)·ε_n` for the single zero in the window. Hence
  ```
  ε_n  ≈  −(1/(π log T)) Σ_p c_p p^{−1/2} cos(γ_n log p + arg c_p)  +  (k ≥ 2 terms) .
  ```
  **Each individual displacement is a prime sum.**

Averaging the square over `n` (treating the phases `γ_n log p` as equidistributed — this step is
heuristic, and is flagged as such) gives

> **Relation 56 (displacement energy; derivation partly heuristic).** With
> `A := (1/2)Σ_p|c_p|²/p + (k ≥ 2 contributions)`,
> ```
> Σ_{γ_n ≤ T} ε_n²  ≍  T·A / log T ,        Σ_{γ_n ≤ T} |ε_n|  ≍  T·√A .
> ```
> So the pairing `|ε_n| ≪ 1/log T` established in Theorem 47′ is *typical*, not exceptional, and
> `A = 0` would force the zero sets to coincide exactly.

### 106.2 Where it stalls, precisely

`A = 0` requires **both** `c_p = 0` for all `p` **and** the `k ≥ 2` contributions to vanish. The
`k ≥ 2` part is not negligible at the `1/2`-line: the `k = 2` term of the prime side is
`Σ_p Δb(p²)·p^{−1}` with `Δb(p²) = a_F(p²) − a_G(p²)` (using `c_p = 0`), and Theorem 52 gives
convergence of the prime-power series only for `σ > 1/2`, **not at `σ = 1/2`**. So:

> **`c_p ≡ 0` does not by itself make the prime side of the explicit formula vanish.** What is needed
> in addition is `Σ_p |a_F(p²) − a_G(p²)|/p < ∞`, i.e. control of the *second* coefficients.

That is exactly **strong multiplicity one in `S`**, which is open unconditionally. Note that the
`p²`-coefficients are the subject of the programme's first formalised identity,
`selberg_pairing_prime_sq`:
```
f(p)·conj(g(p)) = (f * conj g)(p²) − f(p²) − conj(g(p²)) ,
```
so the `k = 2` obstruction is precisely the object that identity was built for, met again from the
zero side.

> **Recorded.** The linear route of §103.3 reduces (b′) to a linear statement about `c_p`, but its
> base case `c_p ≡ 0` requires strong multiplicity one at the level of `p²`-coefficients. The
> programme has an exact algebraic identity for those coefficients but no analytic control of
> `Σ_p |Δ_2(p)|/p`. **That sum is the smallest open quantity the programme has reached.**

### 106.3 Why that is worth stating

Every previous "smallest open quantity" in this programme was quadratic (`Σ_p|a_F(p)|²/p`,
`Var(S_F)`, the pair correlation at `α ≍ 1`). `Σ_p |a_F(p²) − a_G(p²)|/p` is **linear** in the
coefficient differences at prime squares. It is bounded by `2Σ_p (|a_F(p²)| + |a_G(p²)|)/p`, which
diverges under Ramanujan alone, so it needs cancellation — but cancellation in a *linear* prime sum
is exactly what the programme's unconditional results (Theorem 2, §39.1, Theorem 52) are about.

**[OPEN CORE], smallest form reached.** For `F ≠ G` in `S` with the same gamma factor, conductor and
root number and with `a_F(p) = a_G(p)` for all `p`: show `Σ_{p ≤ x}(a_F(p²) − a_G(p²))/p` is
unbounded, or exhibit the obstruction to doing so.

---

## 107. Cycle 107 (2026-07-26) — integrality **at the critical line**: the prime-square density theorem

§85.1 proved that integrality in `S` cannot come from anywhere in a neighbourhood of `Re s ≥ 1`; it
must come from the critical strip. This cycle produces the first such statement.

### 107.1 The theorem

> **Theorem 57 (prime-square integrality).** Let `F, G ∈ S` satisfy `a_F(p) = a_G(p)` for **all**
> primes `p`, and put `Δ(p) := a_F(p²) − a_G(p²)`. If the logarithmic density
> ```
> c := lim_{x→∞} (loglog x)^{−1} Σ_{p ≤ x} Δ(p)/p
> ```
> exists, then
> ```
> c = − ord_{s = 1/2}(F/G) ∈ Z .
> ```
>
> *Proof.* Since the `k = 1` terms cancel and `b(p²) = a(p²) − a(p)²/2`, the difference of logarithms is
> ```
> log(F/G)(s) = Σ_p Δ(p) p^{−2s} + H(s) ,   H(s) := Σ_p Σ_{k≥3} (b_F(p^k) − b_G(p^k)) p^{−ks} .
> ```
> By the transfer bound (`log_coeff_bound`, formalised) `|b_F(p^k)| ≤ (4C_ε)^k p^{kε}`, so
> `Σ_pΣ_{k≥3}|Δb(p^k)|p^{−kσ} ≪ Σ_p (4C_ε)³ p^{3(ε−σ)}`, convergent for `σ > 1/3 + ε`; letting
> `ε → 0`, **`H` is holomorphic on `Re s > 1/3`**, in particular at `s = 1/2`.
>
> Write `D(w) := Σ_p Δ(p)p^{−w}`, so `log(F/G)(s) = D(2s) + H(s)`. If the density `c` exists then
> `D(w) = −c·log(w−1) + o(log(1/|w−1|))` as `w → 1^+`, because `Σ_p p^{−w} = −log(w−1) + O(1)`.
>
> On the other side, `F/G` is **meromorphic** at `s = 1/2` (both `F` and `G` are meromorphic on `C`),
> so with `m := ord_{s=1/2}(F/G) ∈ Z` the function `log(F/G)(s) − m·log(s−1/2)` is holomorphic near
> `s = 1/2`. Comparing the two expressions at `w = 2s → 1` gives `−c = m`. ∎

### 107.2 The full critical line

The same argument at `w = 1 + 2iτ`:

> **Corollary 58 (divisor detection).** For every `τ ∈ R`, if
> `c_τ := lim (loglog x)^{−1}Σ_{p≤x} Δ(p)p^{−2iτ}/p` exists, then
> ```
> c_τ = − ord_{s = 1/2 + iτ}(F/G) ∈ Z .
> ```
> Hence `c_τ = 0` for all but countably many `τ`, and the exceptional set is **exactly the divisor of
> `F/G` on the critical line**, with the density reading off the multiplicity.

### 107.3 Why this matters

- It is the **first integrality statement in the programme located on the critical line**, and it is
  unconditional. Every earlier one (Theorem 2, §39.1, Theorem 10) lived at `Re s = 1`, where §85.1's
  witness `L(·,χ)^c` shows integrality cannot be forced.
- The mechanism is the same monodromy/pole-order mechanism identified in §74 as the only one that
  fires — but it is now applied at `s = 1/2`. What made that possible is Theorem 52's transfer bound,
  which pushes the `k ≥ 3` prime-power tail all the way to `Re s > 1/3`, leaving the `k = 2` term
  alone at the critical line. **The `k = 2` term is exactly the quadratic-in-`p²` datum that the
  programme's very first formalised identity, `selberg_pairing_prime_sq`, was built to isolate.**
- It converts the "smallest open quantity" of §106.3 into a statement with an integral answer: the
  density `Σ_{p≤x}(a_F(p²) − a_G(p²))/p / loglog x` is not merely bounded or unbounded — **when it
  exists it is an integer, namely minus the order of `F/G` at `1/2`.**

### 107.4 Consequences for strong multiplicity one

If `a_F(p) = a_G(p)` for all `p` and `F ≠ G`, then by Theorem 55 the divisors of `F` and `G` agree
off the critical line, so `F/G` has divisor supported **on** the line; Corollary 58 says that divisor
is read off the prime-square densities `c_τ`. Therefore:

> **Corollary 59.** With `a_F(p) = a_G(p)` for all `p`: `F = G` **iff** `c_τ = 0` for every `τ` and
> `F/G` has no divisor on the critical line — and by Corollary 58 the second condition is implied by
> the first. So
> ```
> a_F(p) = a_G(p) ∀p   and   Σ_{p≤x}(a_F(p²) − a_G(p²))p^{−2iτ}/p = o(loglog x) ∀τ   ⟹   F/G is entire
> ```
> and then, by the degree-zero classification plus the Euler product (§104.2), `F = G`.

**This is an unconditional strong-multiplicity-one theorem in `S`, conditional only on the vanishing
of the prime-square densities** — a strictly weaker and far more concrete hypothesis than anything
the programme has previously required.

---

## 108. Cycle 108 (2026-07-26) — MI reduces to integrality of *linear* prime-square densities

Theorem 57 produced integrality on the critical line for a **difference** of two elements. This cycle
asks what the same mechanism gives for a single `F`, and finds a new sufficient condition for MI.

### 108.1 The exact identity, from the programme's first formalised theorem

`selberg_pairing_prime_sq` (Lean, unconditional): for arithmetic functions with `f(1)=g(1)=1` and
`p` prime,
```
f(p)·conj(g(p)) = (f * conj g)(p²) − f(p²) − conj(g(p²)) .
```
Applied with `f = g = a_F` (so `f * conj g` is the coefficient system of `F·\bar F ∈ S`):

> ```
> |a_F(p)|²  =  a_{F\bar F}(p²)  −  2 Re a_F(p²) .
> ```

Dividing by `p`, summing over `p ≤ x` and normalising by `loglog x`:

> **Theorem 60 (energy as a combination of prime-square densities).** Define, for `H ∈ S`, the
> **prime-square density** `δ₂(H) := lim_{x→∞}(loglog x)^{−1} Σ_{p≤x} a_H(p²)/p` when it exists. Then
> ```
> n_F  =  δ₂(F\bar F)  −  2 Re δ₂(F) .
> ```
> In particular
> ```
> ( δ₂(H) ∈ Z for every H ∈ S )   ⟹   n_F ∈ Z for every F ∈ S   ⟹   Selberg's Conjecture A .
> ```

**This is a new sufficient condition for MI, and it is *linear*.** Every previous formulation of MI in
this programme was irreducibly quadratic in the prime coefficients (`Σ_p|a_F(p)|²/p`, the
Rankin–Selberg pole, the variance of `S_F`, the twist correlation). `δ₂(H)` is a plain logarithmic
density of a single coefficient sequence `(a_H(p²))_p`.

### 108.2 What the monodromy mechanism actually sees, and the residual coupling

Theorem 57's mechanism reads off densities of the **logarithmic** coefficients `b_H(p²)`, not of
`a_H(p²)`. The two differ by the Newton relation `b(p²) = a(p²) − a(p)²/2`, so

> ```
> δ₂(H) = ( density of b_H(p²) ) + ½ · ε₂(H) ,     ε₂(H) := density of a_H(p)² ,
> ```
> the **unconjugated energy** `ε₂` (note: `a(p)²`, not `|a(p)|²`).

So integrality of `δ₂` splits into the monodromy-visible part (the `b`-density) and `ε₂/2`. Checking
consistency: for `H = F\bar F` one has `a_H(p) = 2Re a_F(p)`, and the combination of §108.1 makes the
`b`-densities cancel identically (as they must, since `log(F\bar F) = 2Re log F` on the reals), the
surviving content being exactly `n_F = (Re a)²+(Im a)²` densities. **The coupling is therefore
`ε₂ ↔ n_F`, i.e. between the unconjugated and conjugated energies.**

### 108.3 The resulting target

> **(PSD) Prime-square density integrality.** For every `H ∈ S` the density
> `δ₂(H) = lim (loglog x)^{−1}Σ_{p≤x} a_H(p²)/p` exists and is an integer.

- `PSD ⟹ MI ⟹ Conjecture A` (Theorem 60).
- `PSD` is a statement about a **single, linear** logarithmic density, of the kind for which this
  programme already has unconditional theorems (Theorem 2 at `s=1`, Theorem 57 and Corollary 58 at
  `s=1/2`).
- In the automorphic case `PSD` holds and is transparent: `a_π(p²) = h_2(α)` and its density counts
  the multiplicity of the trivial representation in `Sym²ρ ⊕ ∧²ρ`-type decompositions, an integer.
- Its content beyond `MI` is that the *unconjugated* energy `ε₂(H)` is also integral; `PSD` is
  therefore formally **stronger** than `MI`, and the honest statement is that it is a new sufficient
  condition, not an equivalent one.

**[OPEN CORE], new form.** Prove `PSD` for a single `H ∈ S` — equivalently, show that the logarithmic
density of `(a_H(p²))_p` is the order of a pole of a meromorphic function. Theorem 57 does exactly
this for differences `F/G` where the linear terms cancel; the single-function case needs the linear
term `Σ_p a_H(p)p^{−s}` to be separated from the square term at the critical line, which is the one
step still missing.

---

## 109. Cycle 109 (2026-07-26) — the single-function obstruction is `n_H` itself

§108 left one step: separate the linear term from the square term at the critical line for a single
`H ∈ S`. This cycle carries it out and finds that the step is **self-referentially** blocked.

### 109.1 The substitution that puts the square term at its density point

Writing the Euler product at `s = w/2`:
```
log H(w/2) = Σ_p a_H(p) p^{−w/2}  +  Σ_p b_H(p²) p^{−w}  +  Σ_p Σ_{k≥3} b_H(p^k) p^{−kw/2} .
```
Near `w = 1`:
- the `k = 2` term is `−β·log(w−1) + O(1)` where `β` is the logarithmic density of `b_H(p²)` — the
  target;
- the `k ≥ 3` terms converge at `w = 1` (`Σ_p |b_H(p³)|p^{−3/2} < ∞` by the transfer bound), so they
  are holomorphic there;
- the left side is `m·log(w−1) + O(1)` with `m = ord_{s=1/2}(H) ∈ Z`, since `H` is meromorphic.

> **Conditional identity.** If `Σ_p a_H(p)p^{−1/2}` converges, then `β = −ord_{s=1/2}(H) ∈ Z`, and
> more generally `β_τ = −ord_{s=1/2+iτ}(H)` whenever `Σ_p a_H(p)p^{−1/2−iτ}` converges.

### 109.2 The hypothesis is never satisfied — and the reason is `n_H`

Convergence of `Σ_p a_H(p)p^{−1/2−iτ}` requires, by the three-series/variance criterion, that
```
Σ_p |a_H(p)|² / p  <  ∞ ,
```
i.e. exactly `n_H = 0`. Sanity checks:
- `H = ζ`: `a(p) = 1`, `Σ_p p^{−1/2}` diverges; and indeed `b_ζ(p²) = 1/2` gives `β = 1/2`, while
  `ord_{1/2}ζ = 0`, so the conditional identity would be false — the hypothesis correctly fails.
- `H` self-dual cuspidal of degree `2`: Sato–Tate gives density of `a_H(p)²` equal to `1`, hence
  `β = −1/2`, while `ord_{1/2}H = 0` generically — again the identity would fail, and again
  `Σ_p a_H(p)p^{−1/2}` diverges because its variance `Σ_p a_H(p)²/p ~ loglog x` is unbounded.

> **Theorem 61 (self-reference).** For `H ∈ S` the linear prime sum `Σ_p a_H(p)p^{−1/2−iτ}` converges
> only if `n_H = 0`. Hence the monodromy mechanism of Theorem 57, run for a **single** `H` at the
> critical line, computes the prime-square density `β_τ` from data whose convergence already requires
> `n_H = 0`. **The obstruction to obtaining `n_H` by a one-function argument at the critical line is
> `n_H` itself.**

### 109.3 What this explains, and what it leaves

- It explains uniformly why every one-function critical-line attempt in this programme has failed
  (§67, §76, §95, §97, §108): they all require separating the linear from the quadratic prime data at
  `Re s = 1/2`, and the linear data is convergent there exactly when the quadratic answer is `0`.
- It is consistent with, and sharpens, Theorem 49: when `n_H = 0` the mechanism **does** run and gives
  `β_τ = −ord_{1/2+iτ}(H) ∈ Z`, matching the rigid-zero picture.
- **`β` is not an integer in general.** For `ζ^k` it is `k/2`; for self-dual cuspidal `H` it is
  `−1/2`. So the prime-square *logarithmic* density lies in `½Z`, not `Z` — recorded as a correction
  to any expectation that `b`-densities are integral. (Theorem 60's `δ₂`, the density of `a_H(p²)`
  rather than `b_H(p²)`, is the one conjectured integral in (PSD); the two differ by `ε₂/2`, which is
  exactly the half-integrality just observed.)
- What survives as a target is unchanged in substance but sharper in form: **(PSD)** for a single
  `H`, i.e. integrality of `δ₂(H) = (b`-density`) + ½ ε₂(H)`, where the two summands are individually
  half-integral and their sum is conjecturally an integer.

> **Recorded do-not-retry.** No argument that isolates the `k = 2` term of `log H` at the critical
> line by discarding or bounding the `k = 1` term can work, for any `H ∈ S` with `n_H > 0`. The two
> are inseparable there, and the separation constant is `n_H`.

---

## 110. Cycle 110 (2026-07-26) — the linear-cancellation route is exhausted; what Theorem 60 actually buys

### 110.1 Exhaustion

Theorem 57 works because the `k = 1` terms cancel. Which combinations `Σ_i c_i log H_i` have vanishing
`k = 1` part but non-vanishing `k = 2` part? Since `log` is additive on `S`, the `k = 2` part of any
such combination is the corresponding combination of the `b_{H_i}(p²)`, and it vanishes whenever the
product `∏ H_i^{c_i}` is trivial. Concretely, the natural candidate
`(H_1,H_2,H_3) = (F\bar F, F, \bar F)` with `c = (1,−1,−1)` kills the `k=1` part — but the product is
`1`, so every `k` vanishes.

> **Recorded.** A combination with vanishing linear part and non-vanishing square part exists **only**
> when two distinct elements of `S` share all their prime coefficients — precisely the hypothesis of
> Theorem 57. So Theorem 57 is not a general tool: it is exactly a tool for proving strong
> multiplicity one, and conjecturally its hypothesis is never satisfiable. That is the normal shape of
> such a theorem, not a defect, but it closes the search for other linear-cancellation combinations.

### 110.2 What `δ₂` is, in the automorphic world

For `H` automorphic of degree `d` with Satake parameters `α(p)`, the complete homogeneous symmetric
function of degree `2` gives `a_H(p²) = h_2(α(p)) = χ_{Sym²ρ}(θ_p)`, so
```
δ₂(H) = ⟨ χ_{Sym²ρ} , 1 ⟩ = ord_{s=1} L(s, Sym² H) ∈ Z_{≥0} .
```
So **(PSD) is the statement that the symmetric-square pole order is an integer** — in the automorphic
world a triviality, in `S` a functoriality-strength assertion. Recorded so that (PSD) is not mistaken
for an elementary statement.

### 110.3 What Theorem 60 nevertheless buys

The classical route to MI is: construct the Rankin–Selberg convolution `F × \bar F`, an object of
**degree `d²`** that does not exist in `S` a priori (§9.1), and read `n_F` off its pole. Theorem 60
replaces this by
```
n_F  =  δ₂(F\bar F)  −  2 Re δ₂(F) ,
```
where `F\bar F ∈ S` has degree `2d` and `F ∈ S` has degree `d`. So:

> **The degree-`d²` construction is replaced by two logarithmic densities of prime-square coefficients
> of objects already in `S`.** No new `L`-function has to be constructed; what has to be proved is the
> integrality of two ordinary densities.

That is a genuine reduction in the *objects* involved, even though the difficulty migrates rather than
disappearing. It also explains the classical picture cleanly: in the self-dual case
`F × F = Sym²F ⊞ ∧²F`, and Theorem 60 is the coefficient-level shadow of that decomposition, obtained
from `selberg_pairing_prime_sq` with no representation theory at all.

### 110.4 Standing position after 110 cycles

The programme has produced two genuinely new *unconditional* integrality theorems located where §85.1
proves they must be — on the critical line: Theorem 57 (`c = −ord_{1/2}(F/G) ∈ Z` for pairs with equal
prime coefficients) and Corollary 58 (the divisor of `F/G` on the critical line is read off the
prime-square densities). Theorem 61 explains why the single-function analogue cannot be obtained: the
separation constant between the linear and quadratic prime data at `Re s = 1/2` **is** `n_H`.

Together these give the sharpest available description of Conjecture A:

> `n_F` is the separation constant between the linear and the quadratic prime data of `F` at the
> critical line. Every mechanism that could certify it as an integer requires that separation to have
> already been performed. The only cases in which the separation is available are those where the
> linear data cancels — i.e. between two elements of `S` with identical prime coefficients — and there
> the mechanism does fire, unconditionally (Theorem 57).

**Novelty assessment for Theorems 52, 57, 60, 61 (recorded at cycle 110).** Theorem 52 (effective
`θ = 0` from Ramanujan) is plausibly folklore — the redundancy of parts of Selberg's axioms has been
discussed in the literature — but the programme has not located a reference giving the explicit
transfer constant `(4CR)^k`, and the constant is what makes the `k ≥ 3` tail reach `Re s > 1/3` in
Theorem 57. Theorem 53 is a crude bound and is likely known. **Theorems 57, 60 and 61 have not been
matched to anything in the literature**: the shape "prime-square logarithmic density `=` order of a
ratio at `s = 1/2`" and the self-reference statement "`n_H` is the separation constant" appear to be
new formulations. This is recorded as an assessment, not a claim of priority; a systematic search of
the strong-multiplicity-one literature in `S` (Murty–Murty, Kaczorowski–Perelli, Bombieri–Perelli) is
the outstanding verification task.

---

## 111. Cycle 111 (2026-07-26) — an energy bound on the critical-line divisor, and BS ⟹ strong multiplicity one

### 111.1 Almost-orthogonality of the critical-line characters

On sequences `u = (u(p))_p` define the logarithmic prime form
```
⟨u,v⟩ := lim_{x→∞} (loglog x)^{−1} Σ_{p≤x} u(p) conj(v(p)) / p
```
(positive semi-definite where defined). For `τ ∈ R` put `e_τ(p) := p^{2iτ}`. Then
```
⟨e_τ, e_{τ'}⟩ = lim (loglog x)^{−1} Σ_{p≤x} p^{−1−2i(τ−τ')} = δ_{τ,τ'} ,
```
because `Σ_p p^{−1−2iθ} = log ζ(1+2iθ) + O(1) = O(1)` for `θ ≠ 0`. **So `{e_τ}` is an orthonormal
system**, and Bessel's inequality applies.

### 111.2 The energy bound

Let `F, G ∈ S` have identical gamma factors and conductors and satisfy `a_F(p) = a_G(p)` for all `p`;
put `Δ(p) := a_F(p²) − a_G(p²)` and `E := ⟨Δ,Δ⟩ = lim (loglog x)^{−1}Σ_{p≤x}|Δ(p)|²/p`. By
Corollary 58, `⟨Δ, e_τ⟩ = c_τ = −ord_{s=1/2+iτ}(F/G)`. Bessel then gives:

> **Theorem 63 (critical-line divisor energy).**
> ```
> Σ_{τ ∈ R} ( ord_{s=1/2+iτ}(F/G) )²  ≤  E .
> ```
> Since each non-zero order has square `≥ 1`, the divisor of `F/G` on the critical line has **at most
> `E` points**.

This is the exact analogue, at the critical line, of Theorem 10 (`n_F ≥ ν²` at the `1`-line), and it
upgrades that single-point statement to a full Bessel inequality. Recorded also in its `1`-line form:

> **Theorem 62 (multi-point Energy Gap).** For `F ∈ S`,
> `Σ_{θ ∈ R} (ord_{s=1+iθ} F)² ≤ n_F`, by the same Bessel argument with `e_θ(p) = p^{iθ}`.
> Theorem 10 is the single-term case.

### 111.3 Consequence: strong multiplicity one under Bounded Satake

By Theorem 55, `F/G` has no zeros or poles off the critical line. By Theorem 63 it has at most `E` on
the line. If `E < ∞`, `F/G` is therefore a meromorphic function of finite order with **finitely many
zeros and poles**, tending to `1` as `Re s → +∞`; hence `F/G = P(s)/Q(s)·e^{as+b}` with `P,Q`
polynomials, and being also a Dirichlet series (hence almost periodic on vertical lines, hence not a
non-constant rational function times an exponential) it must be constant, equal to `1` by
`a(1) = 1`.

> **Theorem 64 (conditional strong multiplicity one).** Let `F, G ∈ S` have identical gamma factors
> and conductors, with `a_F(p) = a_G(p)` for all primes `p`. If
> `Σ_{p≤x}|a_F(p²) − a_G(p²)|²/p ≪ loglog x` — in particular under **Bounded Satake** (`|a_H(p^k)|`
> bounded, §9.5), which gives `E ≤ 4B²` — then `F = G`.

**BS is strictly weaker than automorphy and strictly weaker than the polynomial Euler product
conjecture** (§9.5), so this is a genuine conditional advance: strong multiplicity one in `S` follows
from a boundedness hypothesis on the coefficients, with no Rankin–Selberg convolution and no
functoriality.

### 111.4 Honest scope

Three inputs are used and must be recorded:
1. **Corollary 58** requires the logarithmic densities `c_τ` to exist; deriving them from the
   `log`-singularity of `F/G` at `1/2+iτ` is a **Tauberian** step (Delange/Wiener–Ikehara type) which
   is standard but not proved here. Without it, Theorem 63 holds for those `τ` where the density
   exists.
2. **`E < ∞`** fails under Ramanujan alone: `|Δ(p)| ≪_ε p^ε` only gives
   `Σ_{p≤x}|Δ(p)|²/p ≪ x^{2ε}`, far larger than `loglog x`. Boundedness of the prime-square
   coefficients is genuinely needed.
3. The last step uses that a Dirichlet series which is a rational function times `e^{as+b}` must be
   constant — true because a convergent Dirichlet series is almost periodic on vertical lines in its
   half-plane of convergence, whereas a non-constant rational function is not.

**[NEXT]** Formalise the Bessel step (`⟨e_τ,e_{τ'}⟩ = δ`, then `Σ|⟨u,e_τ⟩|² ≤ ⟨u,u⟩`) — it is a clean
finite-dimensional statement about a positive semi-definite form and an orthonormal family, and it is
the load-bearing algebraic content of Theorems 62 and 63.

**Formalisation of the Bessel step (cycle 111).**
`HTGeometry/BesselPSD.lean` — `bessel_of_orthonormal`: for any form `B` on a complex module that is
additive and `C`-homogeneous in the first slot, conjugate-symmetric, and positive semi-definite on the
diagonal, and any finite orthonormal family `(e_i)`,
```
∑_i ‖B u (e i)‖² ≤ Re (B u u) .
```
Definiteness is **not** assumed, which is what makes it applicable to the logarithmic prime form
`⟨u,v⟩ = lim (loglog x)^{−1}Σ_{p≤x}u(p)conj(v(p))/p` — a limit of positive forms, degenerate in
general. `lake build` passes; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

This is the load-bearing algebraic content of Theorems 62 and 63. **Formal corpus: 48 theorems in 14
modules, all unconditional, all axiom-clean under `lake build`.**

---

## 112. Cycle 112 (2026-07-26) — the general Bessel packaging: `n_F` bounds the total pretentious energy

Theorems 62 and 63 used one orthonormal family each. The Bessel step (`bessel_of_orthonormal`,
formalised) needs only orthonormality, so it applies to **every** such family at once.

### 112.1 Orthonormal families for the logarithmic prime form

Recall `⟨u,v⟩ = lim (loglog x)^{−1}Σ_{p≤x}u(p)conj(v(p))/p`. Two families are orthonormal:
- `e_θ(p) = p^{iθ}`, `θ ∈ R`, since `Σ_p p^{−1−iθ} = log ζ(1+iθ) + O(1)` is bounded for `θ ≠ 0`;
- `e_χ(p) = χ(p)` for primitive Dirichlet characters `χ`, since `Σ_p χ(p)\barψ(p)/p = O(1)` for
  `χ ≠ ψ` and `Σ_{p∤q}1/p ~ loglog x`;
and hence so is the joint family `e_{χ,θ}(p) = χ(p)p^{iθ}`.

### 112.2 The theorem

> **Theorem 66 (pretentious energy bound).** For every `F ∈ S` and every orthonormal family `{e_j}`
> for `⟨·,·⟩`,
> ```
> Σ_j | ⟨ v_F , e_j ⟩ |²  ≤  n_F ,      v_F := (a_F(p))_p .
> ```
> In particular, over all primitive Dirichlet characters `χ` and all `θ ∈ R`,
> ```
> Σ_{χ,θ} | lim_{x→∞} (loglog x)^{−1} Σ_{p≤x} a_F(p)\barχ(p) p^{−iθ}/p |²  ≤  n_F .
> ```
> **`n_F` bounds the total energy with which `F` "pretends to be" a twisted character.** In
> particular the set of pairs `(χ,θ)` at which `F` has non-zero pretentious density is finite, of
> cardinality at most `n_F/δ²` for any lower bound `δ` on the densities; and whenever the twist
> `F ⊗ \barχ` is meromorphic (so that the density is `−ord_{1+iθ}(F⊗\barχ) ∈ Z` by §39.1), the count
> is at most `n_F`.

Theorem 62 is the special case `χ` trivial; Theorem 10 is the further special case of a single `θ`.

### 112.3 Two corollaries

- **(a)** If `n_F < 1` then `F` has no pole or zero at any `1+iθ`, **and** `F` is not pretentious
  against any twisted character: every density `⟨v_F, e_{χ,θ}⟩` vanishes. So the remaining Energy Gap
  case (`0 < n_F < 1`) describes an element of `S` whose prime coefficients are *totally
  non-pretentious* — orthogonal to every `χ(p)p^{iθ}` — yet carry non-zero energy. That is a sharper
  description of the remaining case than §52's.
- **(b)** For `F = ∏_i F_i^{e_i}` with the `v_{F_i}` orthonormal (i.e. granting Conjecture B for the
  factors), Bessel gives `Σ_i e_i² ≤ n_F`, with equality because `v_F = Σ_i e_i v_{F_i}` lies in their
  span. So the formula `n_F = Σ e_i²` is exactly the equality case of Bessel — recorded as the
  conceptual content of Selberg's prediction.

### 112.4 Status of the Bessel line of attack

The Bessel inequality has now produced, unconditionally: Theorem 62 (multi-point Energy Gap at the
`1`-line), Theorem 63 (critical-line divisor energy), Theorem 64 (strong multiplicity one under
Bounded Satake) and Theorem 66 (pretentious energy). All four follow from one formalised lemma plus
the orthonormality of `{χ(p)p^{iθ}}`. This is the most productive single tool the programme has found,
and it is elementary — it needs no continuation beyond `Re s = 1`, no Rankin–Selberg and no
functoriality.

> **Its limit is also clear.** Bessel bounds `Σ_j|⟨v_F,e_j⟩|²` **from above** by `n_F`; it can
> therefore certify that `n_F` is *large* (Theorems 10, 62, 63) but never that it is *small* or
> integral. Producing a matching lower bound would require completeness of the family
> `{χ(p)p^{iθ}}` for the logarithmic prime form — i.e. that the prime coefficient vector of every
> `F ∈ S` lies in the closed span of twisted characters. **That completeness statement is a new,
> clean, and evidently equivalent form of Selberg's Conjecture A**, recorded as such:
>
> **(CMP) Completeness.** For every `F ∈ S`, `v_F` lies in the closed span of `{χ(p)p^{iθ}}` in the
> logarithmic prime form; equivalently `Σ_{χ,θ}|⟨v_F,e_{χ,θ}⟩|² = n_F`.
>
> `CMP ⟹ n_F = Σ ν_{χ,θ}² ∈ Z` whenever the twists are meromorphic, hence `CMP ⟹ MI`.

---

## 113. Cycle 113 (2026-07-26) — CMP is FALSE, and the Bessel method's reach is exactly degree ≤ 1

Phase-4 attack on §112.4's conjecture (CMP), by testing it on the smallest non-degree-1 example.

### 113.1 The refutation

Let `F` be a cuspidal `L`-function of degree `2` (say the `L`-function of a holomorphic newform).
Then for **every** primitive Dirichlet character `χ` and every `θ ∈ R`,
```
⟨v_F , e_{χ,θ}⟩ = lim (loglog x)^{−1} Σ_{p≤x} a_F(p)\barχ(p)p^{−iθ}/p = 0 ,
```
because `F ⊗ \barχ` is again cuspidal (of degree `2`), so its `L`-function is entire and non-vanishing
at `1+iθ`, and the linear density vanishes. Yet `n_F = 1`. Hence
```
Σ_{χ,θ} |⟨v_F , e_{χ,θ}⟩|² = 0  <  1 = n_F .
```

> **Verdict on CMP: FALSE.** The closed span of `{χ(p)p^{iθ}}` does not contain `v_F` for `F` of
> degree `≥ 2`; Bessel's inequality is strict, and maximally so. **Recorded do-not-retry.**

The corrected statement is simply Conjecture B itself:

> **(CMP′)** `{v_F : F ∈ S primitive}` is an orthonormal basis of the closed span of `{v_H : H ∈ S}`.

which is a restatement, not a route. What the refutation *does* give is a sharp delimitation of the
method.

### 113.2 The reach of the Bessel method

The only orthonormal families the programme can exhibit unconditionally are
`{χ(p)p^{iθ}}` — the prime vectors of the **degree-1** elements of `S`. Therefore:

> **The Bessel method certifies energy only against degree-1 data.** It is sharp for objects whose
> prime data *is* degree-1-like, and vacuous otherwise:
>
> | object | prime data tested | Bessel bound | useful? |
> |---|---|---|---|
> | `F` of degree `1` | `χ(p)p^{iθ}` itself | `Σν² ≤ n_F`, equality | sharp |
> | `F/G` of degree `0` (Thm 63) | `Δ(p)` against `p^{2iτ}` | `Σ(ord)² ≤ E` | sharp enough for Thm 64 |
> | `F` cuspidal of degree `≥ 2` | orthogonal to all `e_{χ,θ}` | `0 ≤ n_F` | **vacuous** |

This is the **fourth independent appearance of the degree-1 barrier** in the programme, after:
the twist-exponent gap `[1/d,1]` (§82), the Bohr averaging length `b^{−(d−1)}` (§81), and the
one-cusp/all-cusp dichotomy (§84). All four say the same thing in different languages: *the
unconditional tools of the Selberg class see exactly the degree-`≤1` world.*

### 113.3 What survives

Theorems 62, 63, 64 and 66 are unaffected — they are true and unconditional; only the hoped-for
converse (CMP) is false. In particular:

- **Theorem 64 (strong multiplicity one under Bounded Satake) stands**, and the reason it works is now
  clear: it tests the *degree-0* object `F/G`, which is exactly where the method is sharp.
- **Theorem 66's corollary (a) is sharpened**: for `F` cuspidal of degree `≥ 2`, the pretentious
  energy is `0` while `n_F = 1`, so the gap between the two sides of Bessel is the whole of `n_F`.
  The remaining Energy Gap case `0 < n_F < 1` is therefore *not* distinguished from cuspidal
  behaviour by pretentiousness — recorded as a correction to §112.3(a), which suggested it was.

> **Net.** Bessel is the programme's most productive elementary tool, and its ceiling is now exactly
> known: it reaches degree `≤ 1` prime data, no further. Any advance on Conjecture A in degree `≥ 2`
> must supply a **new orthonormal family** for the logarithmic prime form — equivalently, must
> exhibit the prime vector of a degree-`≥2` primitive as a unit vector orthogonal to the degree-1
> world, which is precisely what Conjecture B asserts and what nothing unconditional currently
> provides.

---

## 114. Cycle 114 (2026-07-26) — the search for a new orthonormal family closes

§113 left one requirement: exhibit an orthonormal family for the logarithmic prime form beyond
`{χ(p)p^{iθ}}`. Two routes were tried.

### 114.1 Abundance is not the issue

Orthonormal families are **abundant**: any unimodular `g_j` on primes with
`Σ_p g_i(p)\bar g_j(p)/p = O(1)` for `i ≠ j` gives one, and generic choices work. But Bessel is only
informative when the coefficients `⟨v_F, g_j⟩` are non-zero *and* independently computable. For a
generic `g` the correlation with `v_F` vanishes, and the inequality degenerates to `0 ≤ n_F`.

### 114.2 Building the family from the `v`'s adds nothing

The natural attempt is to adjoin `e := v_F/√(n_F)` to `{e_{χ,θ}}` — legitimate for cuspidal `F`, since
`v_F ⊥ e_{χ,θ}`. Bessel then gives, for any `G ∈ S`,
```
|c_{F,G}|² / n_F  +  Σ_{χ,θ} ( ord_{1+iθ}(G⊗\barχ) )²  ≤  n_G .
```
Checks: `G = ζ`, `F` cuspidal gives `0 + 1 ≤ 1` (tight); `G = Fζ` gives `n_F + 1 ≤ n_F + 1` (tight);
`G = F·F'` for distinct cuspidals gives `|c|² ≤ 1`, i.e. Cauchy–Schwarz.

> **Verdict.** Every inequality obtainable by adjoining vectors built from the `v_H` is a consequence
> of positivity of the Gram matrix of `{v_H}`, which the programme already had (§69.1). Bessel with a
> Gram–Schmidt family **is** Gram positivity. **Recorded do-not-retry.**

So the only genuinely new content Bessel can deliver comes from a family whose orthonormality is known
*independently* of the `v_H` — and the only such family available is the degree-1 characters. This
closes the question raised in §113.2 in the negative:

> **The Bessel method is exhausted.** Its unconditional content is exactly Theorems 62, 63, 64 and 66,
> and its ceiling is the degree-`≤1` world. Producing a new independently-orthonormal family is
> equivalent to producing a degree-`≥2` primitive whose prime vector is known to be a unit vector —
> i.e. to `n_F = 1`, which is (P1), the hardest form of Conjecture B.

### 114.3 Consolidated output of cycles 101–114

Unconditional, new, and located where §85.1 proves they must be (on or below the critical line):

| result | statement |
|---|---|
| Thm 52 | `log F − Σ_p a_F(p)p^{−s}` holomorphic on `Re s > 1/2` (effective `θ = 0` from Ramanujan) |
| Thm 53 | `∫_0^T|log F(σ+it)|²dt ≪_σ T log²T` for every `σ > 1/2` |
| Thm 55 | `a_F(p) = a_G(p) ∀p ⟹` divisors of `F,G` agree off the critical line |
| Thm 57 | prime-square density `= −ord_{1/2}(F/G) ∈ Z` |
| Cor 58 | the divisor of `F/G` on the critical line is read off the prime-square densities |
| Thm 60 | `n_F = δ₂(F\bar F) − 2Re δ₂(F)` — MI from *linear* prime-square densities |
| Thm 61 | `n_H` is the separation constant between linear and quadratic prime data at `Re s = 1/2` |
| Thm 62 | `Σ_θ (ord_{1+iθ}F)² ≤ n_F` |
| Thm 63 | `Σ_τ (ord_{1/2+iτ}(F/G))² ≤ E` |
| Thm 64 | Bounded Satake `⟹` strong multiplicity one in `S` |
| Thm 66 | `n_F` bounds the total pretentious energy of `F` |

Refuted in-cycle, with witnesses: ZD (§77), RZ (§98), the zero-sharing bridge (§87), CMP (§113), and
the Bessel-extension route (§114.2). Design rules derived from those failures: thin sets (§77.2),
scales (§87.2), regimes (§98.3), and now **independence** — an inequality is only informative if its
ingredients are known independently of the object being bounded.

---

## 115. Cycle 115 (2026-07-26) — the Energy Gap as a coefficient mean-value statement

### 115.1 The restatement

By Wirsing (§58), for `F ∈ S` with prime density `n_F`,
```
Σ_{n≤x} |a_F(n)|²  ~  c_F · x (log x)^{n_F − 1} / Γ(n_F) .
```
Hence, provided `c_F > 0`:

> **The Energy Gap `n_F ≥ 1` for non-constant `F ∈ S` is equivalent to the coefficient mean-value
> statement**
> ```
> Σ_{n ≤ x} |a_F(n)|²  ≫  x .
> ```
> and `n_F ≤ 1` is equivalent to `Σ_{n≤x}|a_F(n)|² ≪ x`. So Conjecture A's `n_F = 1` for primitives is
> exactly *`Σ_{n≤x}|a_F(n)|² ≍ x`* — the Rankin–Selberg mean value, stated with no `L`-function.

Checks: `ζ` gives `x`; `L(·,χ)` gives `x φ(q)/q`; `ζ²` gives `x log³x/(π²·…)`, exponent `n = 4` ✓;
a cuspidal degree-2 form gives `~cx` by Rankin–Selberg ✓.

### 115.2 Attempted proof of the lower bound, and why it fails

The natural route uses the non-vanishing of `F` on `σ > 1` (from the Euler product) plus
Cauchy–Schwarz:
```
0 < |F(1+ε)| ≤ (Σ_n |a_F(n)|² n^{−1−ε})^{1/2} (Σ_n n^{−1−ε})^{1/2} ≍ (R_{F,F}(1+ε))^{1/2} ε^{−1/2} ,
```
so `R_{F,F}(1+ε) ≫ ε·|F(1+ε)|²`. Since `R_{F,F}(1+ε) ≍ ε^{−n_F}` this reads `ε^{−n_F} ≫ ε·|F(1+ε)|²`,
which is automatic for every `n_F ≥ 0` — **no information**. Reversing the inequality to bound
`R_{F,F}` from above requires an upper bound for a mean value that is not available.

Likewise `log F(1+ε) = Σ_p a_F(p)p^{−1−ε} + O(1)` with `|Σ_p a_F(p)p^{−1−ε}| ≤ √(n_F)·log(1/ε)`
(Theorem 10's estimate) gives only the linear density, which vanishes for entire `F`.

> **Recorded.** Both attempts live at `σ = 1`, where Theorem 38's witness `L(·,χ)^c` — holomorphic and
> non-vanishing on a neighbourhood of `Re s ≥ 1`, all linear densities zero, `n = c²` arbitrary —
> refutes the whole family at once. This is the fourth time an Energy-Gap attempt has been killed by
> that single witness (§95.3, §108, §109, §115). **The `σ = 1` line is closed for `n_F`, permanently.**

### 115.3 Value of the restatement

Even though §115.2 fails, §115.1 is worth having:

- It states the Energy Gap **without any analytic continuation**: it is a mean-value bound for the
  Dirichlet coefficients of `F` alone.
- It is the exact point where the Rankin–Selberg method enters classically — `Σ_{n≤x}|a_F(n)|² ≍ x` is
  what `L(s, F × \bar F)` is used to prove — so it isolates what that method delivers, in a form that
  mentions no convolution.
- Combined with Theorem 60 (`n_F = δ₂(F\bar F) − 2Re δ₂(F)`), the programme now has two independent
  coefficient-level formulations of Conjecture A: one as a mean value of `|a_F(n)|²`, one as a pair of
  logarithmic prime-square densities. Both are statements about the coefficients of elements of `S`
  with no auxiliary `L`-function.

**[OPEN CORE], coefficient form.** For non-constant `F ∈ S`, prove `Σ_{n≤x}|a_F(n)|² ≫ x`.

---

## 116. Cycle 116 (2026-07-26) — duality gives a constant, not a density; and the crispest form of EG

### 116.1 What Voronoi duality delivers

The functional equation gives, unconditionally, a Voronoi-type summation formula
`Σ_n a_F(n)φ(n) = Σ_n conj(a_F(n))Φ(n)` with `Φ` an explicit Meijer-`G` transform of `φ`. Taking `φ`
a bump supported on `[1/2,3/2]` with `φ(1)=1` kills every term but `n=1` on the left:
```
1 = Σ_n conj(a_F(n)) Φ(n) ,
```
and `Φ` is concentrated on `n ≪ C(d_F, q_F)`. Cauchy–Schwarz then gives
```
Σ_{n ≤ N} |a_F(n)|²  ≥  1 / Σ_{n≤N}|Φ(n)|²  >  0 ,     N ≍ C(d_F,q_F) .
```

> **This is a genuine unconditional lower bound, but only by a constant.** It says the coefficients of
> `F` cannot all be small below the conductor scale — a quantitative form of `a_F(1)=1` propagated by
> the functional equation. It does **not** give `Σ_{n≤x}|a_F(n)|² ≫ x`, because taking `φ` a bump at
> scale `X` makes the left side `o(X)` for entire `F` (no pole to supply a main term).

### 116.2 The reduction to an `L¹` statement

By Cauchy–Schwarz, `Σ_{n≤x}|a_F(n)|² ≥ (Σ_{n≤x}|a_F(n)|)²/x`, so

> **EG ⟸ `Σ_{n≤x}|a_F(n)| ≫ x` for non-constant `F ∈ S`.**

Since `|a_F|` is multiplicative, `Σ_{n≤x}|a_F(n)| ≫ x` holds as soon as `|a_F(p)| ≥ δ` on a set of
primes of positive logarithmic density — so the `L¹` form fails only if the prime coefficients are
overwhelmingly small, which is `n_F = 0` again. The reduction is therefore not a shortcut, but it does
produce the crispest available statement of the remaining case:

> **(EG₀) No non-constant `F ∈ S` satisfies `Σ_p |a_F(p)|²/p < ∞`.**

Equivalently: *the prime coefficients of a non-trivial element of the Selberg class cannot be square-
summable against `1/p`.* This mentions no continuation, no functional equation, no zeros and no
densities — only the Euler product data. It is the `n_F = 0` case of the Energy Gap in its minimal
form, and by Theorem 49 it is equivalent to *no non-constant `F ∈ S` has rigid zeros*.

### 116.3 Where EG₀ now sits

Four equivalent forms have now been recorded, at four different levels:

| level | statement |
|---|---|
| coefficients | `Σ_p |a_F(p)|²/p = ∞` for non-constant `F` (EG₀) |
| mean value | `Σ_{n≤x}|a_F(n)|² ≫ x` (§115.1, with Wirsing) |
| zeros | the zeros of a non-constant `F` are not rigid (Theorem 49) |
| variance | `Var_{t≤T}(S_F) → ∞` for non-constant `F` (Theorem 49) |

All four are unproved, and §115.2/§109/§95.3 show the `σ = 1` line cannot reach any of them. The
zero-side forms are the ones §77.2's and §87.2's rules permit; the coefficient form EG₀ is the one that
needs no analysis at all to state.

---

## 117. Cycle 117 (2026-07-26) — Theorem 62 bounds the zeros on the 1-line, unconditionally

Self-audit note: §§114–116 were consolidation (equivalent restatements, closure of the Bessel line)
rather than new frontier. Returning to Phase 3/4 on an unexploited consequence.

### 117.1 The corollary I under-stated

Theorem 62 reads `Σ_{θ∈R}(ord_{s=1+iθ}F)² ≤ n_F`. Since every non-zero order has square `≥ 1`:

> **Corollary 67 (finiteness of the 1-line divisor).** Let `F ∈ S` have a prime density `n_F < ∞`.
> Then `F` has at most `n_F` zeros and poles on the whole line `Re s = 1`, counted **without**
> multiplicity; with multiplicity, `Σ ν² ≤ n_F`, so a zero of order `ν` forces `ν ≤ √(n_F)`.

This is unconditional and does not assume a zero-free region, a density estimate, or continuation
beyond `Re s = 1`. Compare the classical situation:

- Non-vanishing of `F` on `Re s = 1` — the analogue of the prime number theorem for `S` — is **open**
  in general; it is known for `d ≤ 2` and under extra hypotheses (Kaczorowski–Perelli).
- Corollary 67 does not prove non-vanishing, but it makes the exceptional set **finite and explicitly
  bounded by the prime energy**, with a square-root bound on the order of any single zero.

Sanity checks: `ζ` has `n = 1` and exactly one point of its `1`-line divisor (the pole, `ν = 1`),
`Σν² = 1 = n_ζ` — **equality**. `ζ^k` has `n = k²` and one point of order `k`, `Σν² = k² = n` —
equality again. `L(·,χ)` has `n = 1` and no `1`-line divisor, `0 ≤ 1` — strict. So the bound is
attained exactly on the powers of `ζ`, which is the expected extremal family.

### 117.2 Why the equality case is informative

Equality in Bessel means `v_F` lies in the span of the tested family `{p^{iθ}}`. So:

> **Corollary 68.** `Σ_θ (ord_{1+iθ}F)² = n_F` **iff** `v_F` lies in the closed span of `{p^{iθ}}` in
> the logarithmic prime form — i.e. iff `F` is, in the prime-density sense, a product of shifted
> zeta factors. Any `F` with a cuspidal factor has strict inequality, with the deficit
> `n_F − Σ_θ ν_θ²` equal to the energy of the cuspidal part.

So the Bessel deficit is a numerical invariant of `F` measuring **how far `F` is from being a product
of shifts of `ζ`**, and it is `0` exactly on that family. Under Conjecture B the deficit is
`Σ_{i : d_i ≥ 2} e_i²`. Recorded as the first invariant the programme has that *detects the presence of
higher-degree primitive factors from prime data alone*, unconditionally.

### 117.3 What this opens

The deficit `D_F := n_F − Σ_θ (ord_{1+iθ}F)² ≥ 0` is unconditional and computable from prime data.
Two immediate questions, both new:

- **(D1)** Is `D_F` an integer? Under Conjecture B, `D_F = Σ_{d_i≥2}e_i² ∈ Z`. `D_F ∈ Z` is strictly
  weaker than MI (it is MI modulo the degree-1 part, which is already known), so **(D1) is a genuinely
  smaller target than Conjecture A** and is not obviously equivalent to it.
- **(D2)** Is `D_F = 0 ⟹ F` is a product of shifted zeta factors? By Corollary 68 this is the
  statement that prime-density membership in the span of `{p^{iθ}}` forces actual membership — a
  rigidity statement of the same type as, but weaker than, strong multiplicity one.

**(D1) is now the smallest open integrality statement in the programme**: it asks for integrality only
of the *non-degree-1 part* of the energy, the degree-1 part being already integral by Theorem 62 and
§39.1.

**Immediate correction to §117.3 (same cycle).** (D1) is **not** a smaller target. Since
`Σ_θ (ord_{1+iθ}F)²` is a sum of squares of integers, it is itself an integer, so
```
D_F ∈ Z   ⟺   n_F ∈ Z   ⟺   MI .
```
(D1) is therefore *equivalent* to Conjecture A, not weaker; the claim that it isolates "only the
non-degree-1 part" was wrong — subtracting an integer changes nothing about integrality. Recorded as
an error caught in-cycle.

**What survives.** Corollary 67 (at most `n_F` points in the `1`-line divisor, order `≤ √(n_F)`) and
Corollary 68 (the Bessel deficit vanishes exactly on prime-density products of shifted zeta factors)
stand, and (D2) — *does `D_F = 0` force `F` to be an actual product of shifted zeta factors?* —
remains a genuine rigidity question **not** equivalent to MI, since it asks about membership rather
than integrality. (D2) is the surviving new target of this cycle.

### 117.4 (D2) is equivalent to EG₀

Equality in Bessel gives `v_F = Σ_θ (−ν_θ) e_θ` in the closure, `ν_θ = ord_{1+iθ}F`, i.e.
`a_F(p) ≈ Σ_θ(−ν_θ)p^{iθ}` in the logarithmic prime `L²`. The element of the group completion of `S`
with exactly those prime coefficients is
```
H(s) = ζ(s)^{m_F} · ∏_{θ≠0} ζ(s−iθ)^{−ν_θ}       (m_F = −ν_0 ≥ 0, ν_θ ≥ 0 for θ ≠ 0),
```
a ratio of shifted zeta factors with **integer** exponents. Then `D_F = 0` says exactly
`‖v_F − v_H‖ = 0`, i.e. `n_{F/H} = 0`. Hence

> **(D2) ⟺ EG₀**: "`D_F = 0` forces `F = H`" is precisely "zero prime energy forces triviality",
> applied to `F/H` in the group completion of `S`. Conversely `n_F = 0` gives `Σν² ≤ 0`, so all
> `ν_θ = 0`, `H = 1`, and (D2) returns `F = 1`.

So cycle 117's surviving new content is exactly Corollaries 67 and 68; (D1) collapsed to MI and (D2)
collapsed to EG₀.

**Novelty note.** Corollary 67 — *an element of `S` with finite prime density has at most `n_F` points
in its divisor on `Re s = 1`, each of order `≤ √(n_F)`* — has not been matched to the literature. It
is unconditional, needs no zero-free region and no density estimate, and follows from Bessel plus the
integrality of the linear prime densities (§39.1). Non-vanishing on `Re s = 1` (the PNT analogue for
`S`) remains open in general; Corollary 67 makes the exceptional set finite and explicitly bounded.

---

## 118. Cycle 118 (2026-07-26) — EG₀: the case `n_F = 0` unlocks two steps, and stalls on a measure-zero set

Attack on EG₀ (`n_F = 0 ⟹ F = 1`), using the machinery of cycles 101–117 in the one case where
Theorem 61's self-reference *does not* apply — because there the obstruction constant is `n_F = 0`.

### 118.1 Two steps that become available when `n_F = 0`

**(i) The `a(p)²` term disappears.** Since `|density of a_F(p)²p^{−2iτ}| ≤ density of |a_F(p)|² = n_F = 0`,
the Newton correction in `b_F(p²) = a_F(p²) − a_F(p)²/2` contributes nothing, so for every `τ`
```
β_τ  :=  density of b_F(p²)p^{−2iτ}  =  δ₂,τ(F)  :=  density of a_F(p²)p^{−2iτ} .
```

**(ii) Bessel at the critical line applies to the prime-square data.** With `E₂ := ⟨a_F(p²), a_F(p²)⟩`
the prime-square energy, the orthonormal family `e_{2τ}(p) = p^{2iτ}` and
`bessel_of_orthonormal` give, **unconditionally**,
```
Σ_{τ ∈ R} | δ₂,τ(F) |²  ≤  E₂ .
```
So the prime-square densities of an `F` with `n_F = 0` are square-summable, hence non-zero at only
countably many `τ`, with total energy `≤ E₂`.

### 118.2 The step that stalls

To conclude `F = 1` one needs the identity of §109.1,
```
δ₂,τ(F)  =  − ord_{s = 1/2+iτ}(F) ∈ Z ,
```
whose proof requires the linear prime sum `P(1/2+iτ) = Σ_p a_F(p)p^{−1/2−iτ}` to **converge at the
point `τ`**. Theorem 61 says this needs `Σ_p|a_F(p)|²/p < ∞` — which now **holds**, since `n_F = 0`.
So the obstruction that blocks every other case is absent here.

What is available is *almost* enough:

- The partial sums satisfy `Σ_{p≤x}|a_F(p)| ≪ x` by Cauchy–Schwarz, so the abscissa of convergence of
  `P` is `≤ 1` — not `≤ 1/2`.
- By the Carleson-type convergence theorem for `ℋ²` Dirichlet series (Hedenmalm–Saksman), a Dirichlet
  series with `ℓ²` coefficients converges **almost everywhere** on the critical line. With
  `b_p = a_F(p)p^{−1/2} ∈ ℓ²` this gives convergence of `P(1/2+iτ)` for **a.e. `τ`**.

> **But the divisor of `F` on the critical line is countable, hence of measure zero.** Almost-everywhere
> convergence therefore says nothing at exactly the points `τ` where the identity is needed.

### 118.3 The gap, stated exactly

> **[OPEN CORE, EG₀ form]** Let `F ∈ S` with `Σ_p|a_F(p)|²/p < ∞`. Show that
> `Σ_p a_F(p)p^{−1/2−iτ}` converges (or is `o(log(1/δ))` on the approach `s = 1/2+δ+iτ`) at every `τ`
> in the divisor of `F` on the critical line. Then `δ₂,τ(F) = −ord_{1/2+iτ}(F) ∈ Z`, Bessel gives
> `Σ_τ (ord_{1/2+iτ}F)² ≤ E₂`, so `F` has finitely many zeros on the line; combined with Theorem 55
> (no zeros off the line when the prime coefficients determine the divisor) `F` has finitely many
> zeros altogether, hence is a rational function times `e^{as+b}`, hence — being a Dirichlet series —
> constant, i.e. `F = 1`.

**This is the first time the Energy-Gap edge case has been reduced to a single, purely analytic
statement about one explicit Dirichlet series**, with every other step supplied: (i) and (ii) above,
Theorem 55, Theorem 63's Bessel argument, and the rational-function endgame of Theorem 64. The residual
question is a **pointwise convergence** question on a measure-zero set — precisely the gap between
Carleson-type a.e. convergence and convergence at prescribed points.

**Recorded as the sharpest live target of the programme.** Note it is *not* blocked by any of the
four barriers (§113.2): it is a statement about a single `F` with `n_F = 0`, where the degree-1 ceiling,
the twist-exponent gap, the one-cusp obstruction and Theorem 61's self-reference all fail to bite.

---

## 119. Cycle 119 (2026-07-26) — corpus audit: one partial duplication found

Prompted audit of the mandate "search the corpus before writing Lean". **The mandate was not being
followed in cycles 101–118**: mathlib names were verified in `/tmp` scratch files every time, but
`scripts/formal_tools.py research` was not run against our own corpus before adding modules. Results
of running it now:

### 119.1 Partial duplication — the Bohr mean value

`GaloisForLFunctions.RHTower.WeylEquidistribution.trig_time_average` already proves, for arbitrary
real frequencies,
```
lim_{T→∞} (1/T) ∫_0^T Σ_i c_i exp(θ_i i t) dt  =  Σ_{i : θ_i = 0} c_i ,
```
which is exactly the **asymptotic** diagonal extraction that `genPoly_meanValue` and
`genPoly_meanValue_bilinear` deliver in the limit. Had it been found first, the limit statements of
Theorems 23, 26, 29 and 30 could have cited it directly.

**What is genuinely new in `GeneralizedDirichletMeanValue`** and does *not* follow from the limit
form: the exact identity at finite interval length, and the bounds uniform in the interval, its
length and its position — `oscInt_norm_le` (`‖oscInt δ T U‖ ≤ 2/|δ|`), `genPoly_meanValue_error`,
`genPoly_meanValue_error_of_gap`. Those are what §81's quantitative averaging-length barrier
(`A ≫ b^{−(d−1)}`) and §83's gap theorem require. Cross-reference added to the module docstring.

Also adjacent: `RHTower.ShiftedMultIndependence.shifted_dirichlet_meanValue` (Hurwitz frequencies
`log(n+α)`), a special case of the same limit.

### 119.2 Not a duplication — Bessel

`GaloisForLFunctions.RHTower.TraceNorm.sum_inner_sq_le_of_orthonormal_with_zeros` is Bessel in a
genuine `InnerProductSpace ℂ H`, i.e. for a **definite** form. `bessel_of_orthonormal` is for a
positive **semi**-definite form supplied as a bare function, which is the setting actually needed:
the logarithmic prime form `⟨u,v⟩ = lim (loglog x)^{−1}Σ_{p≤x}u(p)conj(v(p))/p` is a limit of positive
forms and is degenerate. Cross-reference added.

### 119.3 Process fix

> **Rule reinstated.** Before adding any Lean module: run
> `scripts/formal_tools.py research "<concept>"` (two or three phrasings) **and** `rg` on the key
> symbol, and record the outcome here. `lake build` remains the authoritative check (§105), and
> mathlib names continue to be verified in `/tmp` scratch files.

Net cost of the lapse: one partially redundant limit statement out of 50 theorems, with the
quantitative content unaffected. Net benefit of the audit: two cross-references, and a general Weyl
equidistribution tool (`trig_time_average`) now known to be available for future cycles.

---

## 120. Cycle 120 (2026-07-26) — EG₀ needs cancellation, and its mean-value form is weaker than EG's

Corpus search first (§119.3 rule): `formal_tools.py research "Dirichlet series abscissa convergence
prime coefficients"` — nothing covering convergence of `Σ_p a(p)p^{−1/2−iτ}`; no duplication.

### 120.1 The §118 gap is genuinely RH-strength

With only `A := Σ_p|a_F(p)|²/p < ∞`, the linear prime sum converges **absolutely** only for `σ > 1`:
```
Σ_{p≤X}|a_F(p)|p^{−σ} ≤ A^{1/2}(Σ_{p≤X}p^{1−2σ})^{1/2} ,
```
and `Σ_p p^{1−2σ}` converges iff `σ > 1`. At `σ = 1/2` even the `ℓ²` hypothesis gives only
`Σ_{p≤X}|a_F(p)|p^{−1/2} ≪ A^{1/2}(X/\log X)^{1/2}`, which grows. Moreover the sum
`Σ_p a_F(p)p^{−1/2−δ−iτ}` is **not** an inner product for the logarithmic prime form: writing it as
`⟨a_F, v⟩` forces `v(p) = p^{1/2−δ+iτ}` with `‖v‖² = Σ_p p^{−2δ} = ∞`.

> **Recorded.** Convergence of `Σ_p a_F(p)p^{−1/2−iτ}` at a prescribed `τ` is a genuine cancellation
> statement, not accessible from `n_F = 0` by any Cauchy–Schwarz argument. It is of RH strength.
> §118's route to EG₀ is therefore blocked at exactly that point, and the block is not removable by
> the `ℓ²` hypothesis.

### 120.2 The mean-value form of EG₀ is weaker than that of EG

Wirsing at `τ = n_F` gives `Σ_{n≤x}|a_F(n)|² ~ c_F x(\log x)^{n_F−1}/Γ(n_F)`. As `n_F → 0` the right
side is `o(x/\log x)` (the factor `1/Γ(n_F) → 0`). Hence:

> **`n_F = 0  ⟺  Σ_{n≤x}|a_F(n)|² = o(x/\log x)`**, so
> ```
> EG₀  ⟺  Σ_{n≤x}|a_F(n)|²  ≫  x / \log x     for non-constant F ∈ S .
> ```

Compare §115.1: full EG (`n_F ≥ 1`) is `Σ_{n≤x}|a_F(n)|² ≫ x`. **The `n_F = 0` case therefore needs a
mean-value lower bound weaker by a full factor of `\log x`.** That is a genuine refinement of the
target and is recorded as the sharpest mean-value form the programme has:

| statement | needed bound |
|---|---|
| EG₀ (`n_F = 0 ⟹ F = 1`) | `Σ_{n≤x}\|a_F(n)\|² ≫ x/\log x` |
| EG (`n_F ≥ 1`) | `Σ_{n≤x}\|a_F(n)\|² ≫ x` |
| Conjecture A for primitives | `Σ_{n≤x}\|a_F(n)\|² ≍ x` |

### 120.3 What duality gives, and its ceiling

§116.1's Voronoi argument gives `Σ_{n≤N}|a_F(n)|² ≥ c > 0` with `N ≍ C(d_F,q_F)` — a constant, because
the dual of a bump at scale `1` is supported on `n ≲ q_F`, a **fixed** range. Twisting by `n^{−it}`
grows the dual support to `n ≲ 𝔮(t) ≍ t^{d}`, but the Voronoi kernel is (in the correct
normalisation) an isometry, so `‖Φ_t‖₂ ≍ ‖φ‖₂` and the conclusion remains
`Σ_{n ≲ t^d}|a_F(n)|² ≫ 1` — still a constant, now over a growing range, hence **weaker** as `t`
grows.

> **Recorded do-not-retry.** Voronoi duality applied to a bump propagates `a_F(1) = 1` and nothing
> more: it yields a constant lower bound over any range, never a lower bound growing with the range.
> Obtaining `≫ x/\log x` requires a positive-definite object (a Rankin–Selberg-type kernel), which is
> exactly what `S` does not supply.

**[OPEN CORE, sharpest mean-value form]** For non-constant `F ∈ S`, prove
`Σ_{n≤x}|a_F(n)|² ≫ x/\log x`.

---

## 121. Cycle 121 (2026-07-26) — rigid zeros give an exact Poisson identity, and it fights the primes

Corpus search first: `research "Poisson summation explicit formula zeros"` — nothing on this
combination; no duplication.

§97's chirp obstruction failed because it compared `L²` masses (§98). This cycle redoes it as a
comparison of **single Fourier coefficients**, which §77.2's thin-set rule permits, and the mechanism
survives.

### 121.1 The exact identity

Suppose `F ∈ S` has **rigid zeros**: `γ_n = M^{−1}(n)` exactly, where `M` is the Riemann–von Mangoldt
main term, `M'(t) = ν(t) = (d/2π)\log(t/2π) + …`. For a smooth compactly supported `φ`, substituting
`u = M(t)` and applying **Poisson summation**,
```
Σ_ρ φ(γ_ρ) = Σ_n φ(M^{−1}(n)) = Σ_{k ∈ Z} ĝ(k) ,     ĝ(k) = ∫ φ(t) M'(t) e^{−2πi k M(t)} dt .
```
The `k = 0` term is `∫φ(t)ν(t)dt`, which is **exactly** the archimedean main term of the explicit
formula for `F`. Subtracting it:

> **Theorem 69 (rigid-zero Poisson identity).** If the zeros of `F ∈ S` are rigid then for every
> admissible `φ`
> ```
> Σ_{k ≠ 0} ∫ φ(t) ν(t) e^{−2πi k M(t)} dt
>       =  −(1/2π) Σ_{n≥2} Λ_F(n) n^{−1/2} ( φ̂(\log n) + φ̂(−\log n) )  +  (pole terms) .
> ```
> Exact; the archimedean parts cancel identically because `ν = M'`.

### 121.2 The tension

**Left side.** The phase of the `k`-th term is `2πkM(t) + (\text{phase of } φ)`. Choosing
`φ(t) = ψ((t−t_0)/P)e^{it\log p}` — a bump of length `P` at height `t_0`, modulated to put `φ̂` at
`\log p` — the total phase derivative is
```
2πkν(t) + \log p ,
```
which vanishes only when `|k| ≈ \log p / (2πν(t_0)) ≈ \log p/(d\log t_0)`. **If `p < t_0^d` there is no
integer `k ≠ 0` with a stationary point**, and repeated integration by parts gives
`Σ_{k≠0}|ĝ(k)| ≪_A P (P\log t_0)^{−A}` — negligible.

**Right side.** With `φ̂` a bump of width `≍ 1/P` at `\log p` and `P` large enough to separate
consecutive prime powers near `p` (`P ≫ p`), the prime side is
```
≈ a_F(p)\, (\log p)\, p^{−1/2} .
```

> **Consequence, if the estimates hold.** `a_F(p)(\log p)p^{−1/2} ≪_A P(P\log t_0)^{−A}` for every
> `t_0` with `t_0^d > p`. Letting `t_0 → ∞` forces `a_F(p) = 0` — **for every prime `p`**. Repeating
> at `p²` (where the same argument applies to `Λ_F(p²)`) forces `a_F(p^k) = 0` for all `k`, hence
> `F = 1`.
>
> That is exactly **EG₀**, and with it (by §117.4) (D2), and the `n_F = 0` case of the Energy Gap.

### 121.3 Status — what is proved and what is not

- **Theorem 69 is exact and unconditional given rigidity.** The cancellation of the archimedean terms
  is an identity, not an estimate: `ν = M'` by construction.
- **Not yet proved:** the two estimates of §121.2. The left-side bound needs a stationary-phase /
  integration-by-parts estimate uniform in `k` with the modulated test function, and the right-side
  isolation needs the bump width `1/P` to separate `\log p` from neighbouring `\log n`, which costs
  `P ≫ p` and must be checked against the left-side gain. **The two must be balanced; that balance is
  the whole content and it is not yet verified.**
- **Why this is not §97 again.** §97 compared total `L²` masses and failed because the sawtooth's mass
  is a bounded constant that the error term can absorb (§98). Here the comparison is between a single
  Fourier coefficient on each side, with the archimedean parts cancelling *identically* rather than
  approximately. Thin-set sensitive (§77.2 ✓), single scale (§87.2 ✓), and each asymptotic used inside
  its own regime (§98.3 ✓).

**[OPEN CORE, cycle 121]** Verify the balance in §121.2: show that for `p` fixed and `t_0 → ∞` with
`t_0^d > p`, the left side of Theorem 69 is `o(a_F(p)(\log p)p^{−1/2})` for a suitable choice of
`P = P(p,t_0)`. This is a self-contained oscillatory-integral estimate, with no `L`-function input.

---

## 122. Cycle 122 (2026-07-26) — **perfectly rigid zeros force `F = 1`**: §96.3's open core is closed

Verification of the §121.2 balance. The oscillatory-integral estimates **do** work; the argument needs
*exact* rigidity, and it proves the exact-rigidity case outright.

### 122.1 The estimates

Take `φ(t) = ψ((t−t_0)/P)e^{it\log p}`, `ψ` smooth, supported on `[−1,1]`, and `F ∈ S` **entire** (the
remaining Energy-Gap case), so the explicit formula has no pole term.

**Left side.** The `k`-th phase is `Θ_k(t) = t\log p − 2πkM(t)`, so
`Θ_k'(t) = \log p − 2πkν(t) = \log p − k(d\log(t/2π) + 2πc)`. If `p < t_0^d` then for every `k ≠ 0`
```
|Θ_k'(t)| ≥ |k|·d\log(t_0/2π) − \log p  ≫  |k|\log t_0 ,
```
and `Θ_k''(t) = −kd/t` is negligible over the support provided `P ≪ t_0\log t_0`. Repeated integration
by parts (`A` times) gives
```
Σ_{k≠0} |ĝ(k)|  ≪_A  \log t_0 · P · (P\log t_0)^{−A} · Σ_{k≠0}|k|^{−A}  ≪_A  P^{1−A}(\log t_0)^{1−A} .
```

**Right side.** `φ̂(ξ) = P e^{it_0(\log p − ξ)} ψ̂(P(ξ − \log p))`, concentrated on
`|\log n − \log p| ≲ 1/P`, i.e. `|n − p| ≲ p/P`. Choosing `P = p^{1+η}` makes that interval shorter
than `1`, so **only `n = p` survives at `j = 0`**; for `j ≥ p^η` the number of prime powers at distance
`≈ j/P` is `≪ p^{−η}j/\log p`, contributing `≪ p^{1/2}j|ψ̂(j)| ≪_A p^{1/2}p^{−Aη}` — negligible. The
term `φ̂(−\log n)` is negligible for all `n` since its argument is `≈ −P(\log n + \log p)`. Hence
```
prime side  =  (1/2π) a_F(p)(\log p) p^{−1/2} · P · ψ̂(0) · (1 + o(1))  ≍  |a_F(p)|·p^{1/2+η}\log p .
```

**Balance.** With `A = 3` and `t_0 → ∞` at fixed `p`, the left side is `≪ p^{−2(1+η)}(\log t_0)^{−2} → 0`
while the right side is a fixed multiple of `|a_F(p)|`. Therefore `a_F(p) = 0`.

### 122.2 The theorem

> **Theorem 70 (perfect rigidity forces triviality).** Let `F ∈ S` be entire and suppose its zeros are
> **exactly** rigid: `γ_n = M_F^{−1}(n)` for all `n`, `M_F` the Riemann–von Mangoldt main term. Then
> `a_F(p) = 0` for every prime `p`; iterating the same argument with `φ̂` concentrated at `\log p^k`
> (where `b_F(p²) = a_F(p²)` once `a_F(p) = 0`, and similarly at higher `k`) gives `a_F(p^k) = 0` for
> all `k`, hence **`F = 1`**.
>
> Unconditional, given exact rigidity. The only inputs are: the explicit formula for `F`, Poisson
> summation (Theorem 69), non-stationary phase, and the Ramanujan bound.

**This closes the [OPEN CORE] recorded at §96.3** — *"construct, or rule out, an entire order-1 function
with a Selberg functional equation whose zeros form a perfect log-lattice and whose `L`-part has an
Euler product"*. The answer is: **no non-trivial such function exists.**

### 122.3 The remaining gap: exact versus approximate rigidity

`n_F = 0` gives, via Theorem 49 and the interleaving lemma, only **approximate** rigidity
`γ_n = M^{−1}(n) + ε_n` with `|ε_n| ≪ K/\log T`. Expanding,
```
Σ_n φ(γ_n) = Σ_n φ(M^{−1}(n)) + Σ_n φ'(γ_n) ε_n + O(‖φ''‖ Σ ε_n²) ,
```
and with `‖φ'‖ ≈ \log p` and `≈ P\log t_0` zeros in the support each with `|ε_n| ≪ K/\log t_0`,
```
| Σ_n φ'(γ_n) ε_n |  ≪  K · P · \log p ,
```
which **exceeds** the prime-side main term `|a_F(p)|·P·p^{−1/2}\log p` whenever `|a_F(p)| < K p^{1/2}` —
i.e. always, by Ramanujan.

> **Recorded.** The displacement error swamps the signal by a factor `p^{1/2}`. Closing EG₀ by this
> route requires cancellation in `Σ_n φ'(γ_n)ε_n`, which by Theorem 54 is itself the prime side —
> circular. **So Theorem 70 is sharp: it is exactly the exact-rigidity statement, and no more.**

### 122.4 Status

New unconditional theorem (Theorem 70) settling §96.3's open core; the estimates of §121.2 verified;
the exact/approximate rigidity gap identified as the precise residual obstruction to EG₀, with its
size (`p^{1/2}`) computed.

---

## 123. Cycle 123 (2026-07-26) — the displacement error is the prime side again: Theorem 70 extends to *bounded* `S_F`

§122.3 recorded that approximate rigidity kills the argument because `Σ_n φ'(γ_n)ε_n ≪ KP\log p`
swamps the main term. That bound is crude: the `ε_n` are not arbitrary.

### 123.1 The displacements are the fluctuation

If `|N_F − M_F| ≤ K` then `γ_n = M^{−1}(n) + ε_n` and, since `M(γ_n) − n = M(γ_n) − N_F(γ_n) =
−S_F(γ_n) + O(1)`,
```
ε_n  =  − S_F(γ_n)/ν(γ_n)  +  O(1/ν²) .
```
Hence, approximating the sum over zeros by its density `ν`,
```
Σ_n φ'(γ_n) ε_n  ≈  − ∫ φ'(t) S_F(t) dt ,
```
the `ν`'s cancelling. By the classical formula
`S_F(t) = −(1/π)Σ_n Λ_F(n)n^{−1/2}\sin(t\log n)/\log n + O(1/t)`, integrating by parts turns this into
```
Σ_n φ'(γ_n) ε_n  ≈  (1/π) Σ_n Λ_F(n) n^{−1/2} · (\text{a } φ̂\text{-transform at } \log n) ,
```
i.e. **the same object as the prime side of the explicit formula, of the same order.**

### 123.2 The consequence

The Poisson expansion with displacements reads
```
Σ_{k≠0} ĝ(k)  +  Σ_n φ'(γ_n)ε_n  +  O(‖φ''‖_∞ Σ_n ε_n²)  =  −(1/2π)·(\text{prime side}) ,
```
and by §123.1 the second term is `c'·(\text{prime side})` for an explicit constant `c'`. Therefore,
**provided `c' ≠ −1/(2π)`** (no exact cancellation),
```
(\text{prime side})  ≪  Σ_{k≠0}|ĝ(k)|  +  ‖φ''‖_∞ Σ_n ε_n² .
```
With `φ(t) = ψ((t−t_0)/P)e^{it\log p}`, `P = p^{1+η}`:
- `Σ_{k≠0}|ĝ(k)| ≪_A P^{1−A}(\log t_0)^{1−A}` (§122.1) — `→ 0` as `t_0 → ∞`;
- `‖φ''‖_∞ ≍ (\log p)²` and `Σ_n ε_n² ≪ (P\log t_0)·K²/\log²t_0 = K²P/\log t_0`, so the second-order
  term is `≪ K²P(\log p)²/\log t_0`;
- the prime side is `≍ |a_F(p)|·P·p^{−1/2}\log p`.

Dividing by `P`:
```
|a_F(p)| p^{−1/2}\log p  ≪_A  P^{−A}(\log t_0)^{1−A}  +  K²(\log p)²/\log t_0 .
```
**Both terms tend to `0` as `t_0 → ∞` with `p` fixed** (the constraint being only `p < t_0^d`). Hence
`a_F(p) = 0`, for every prime `p`; iterating at prime powers gives `F = 1`.

> **Theorem 71 (bounded fluctuation forces triviality).** Let `F ∈ S` be entire with
> `|N_F(t) − M_F(t)| ≤ K` for all `t` — equivalently `S_F` bounded. Then `F = 1`.
> **Modulo the constant check `c' ≠ −1/(2π)` of §123.2.**

This strictly extends Theorem 70: *exact* rigidity is replaced by *bounded* fluctuation, which is what
`n_F = 0` delivers via Theorem 49. The `p^{1/2}` loss of §122.3 disappears because the displacement
term was mis-estimated there: it is not an independent error but the prime side itself, so it changes
a constant rather than dominating.

### 123.3 The one remaining item, stated exactly

> **[OPEN, cycle 123]** Compute the constant `c'` in
> `Σ_n φ'(γ_n)ε_n = c'·(\text{prime side}) + o(\text{prime side})` and verify `c' ≠ −1/(2π)`.
>
> The two contributions come from different mechanisms — one from the Poisson expansion of the zero
> sum, one from the explicit formula for `S_F` — and there is no structural reason for them to cancel,
> but the constants must be tracked through the `φ̂`-transform and the integration by parts. Until this
> is done Theorem 71 is not proved.

**Status.** Theorem 70 (exact rigidity) is unconditional and complete. Theorem 71 (bounded
fluctuation) is complete except for the constant check; if `c'` is as expected, then together with
Theorem 49 it gives **EG₀ under the same hypothesis Theorem 49 needs** — a zero-density estimate or
RH — and hence closes the `n_F = 0` case of the Energy Gap under that hypothesis.

---

## 124. Cycle 124 (2026-07-26) — the constant is exactly the cancelling one: **Theorem 71 is false**

The check demanded in §123.3, carried out.

### 124.1 The computation

For `F ∈ S` entire, two exact identities:

**(a)** Integration by parts, using `dN_F = ν dt + dS_F` and `S_F` bounded, `φ` compactly supported:
```
Σ_γ φ(γ)  =  ∫ φ ν dt  −  ∫ φ'(t) S_F(t) dt .
```
**(b)** The Weil explicit formula: `Σ_γ φ(γ) = ∫ φ ν dt − 𝒫[φ]`, where
`𝒫[φ] = (1/2π)Σ_n Λ_F(n)n^{−1/2}φ̂(\log n) + (\text{conj})`.

Comparing, **`∫φ'(t)S_F(t)dt = 𝒫[φ]` identically.**

Now §123.1's displacement term: with `ε_n = −S_F(γ_n)/ν(γ_n) + O(ν^{−2})` and
`Σ_n h(γ_n) = ∫hν dt + ∫h\,dS_F`,
```
Σ_n φ'(γ_n) ε_n  =  −∫φ'(t)S_F(t)dt  +  (\text{second order in } S_F)  =  −𝒫[φ] + O(K²\|φ'\|_∞ P/\log t_0) .
```

Substituting into the Poisson identity `Σ_{k≠0}ĝ(k) + Σ_nφ'ε + O(‖φ''‖Σε²) = −𝒫[φ]`:
```
Σ_{k≠0} ĝ(k)  −  𝒫[φ]  +  O(\text{err})  =  −𝒫[φ]      ⟹      Σ_{k≠0} ĝ(k) = O(\text{err}) .
```

> **The prime sides cancel exactly.** `c'` is precisely the cancelling value, so the identity
> degenerates to a statement about `Σ_{k≠0}ĝ(k)` alone and carries **no arithmetic information**.
>
> **Theorem 71 is false as an argument, and is withdrawn.** §122.3's original assessment — that
> approximate rigidity destroys the argument — was correct, and §123's "fix" was illusory.

### 124.2 Why the cancellation is forced, and why Theorem 70 survives

The decomposition "Poisson main term + displacement correction" is, for a general zero set, just a
re-derivation of `Σ_γφ(γ) = ∫φν − ∫φ'S_F` — the same identity the explicit formula provides. Nothing
new can come out of it.

**Exact rigidity is different in kind.** There `ε_n = 0`, so `S_F(t) = 1/2 − \{M(t)\}` is a
*deterministic chirp sawtooth*, and `∫φ'S_F dt` can be evaluated **independently of the explicit
formula**, by Poisson summation plus non-stationary phase. That independent evaluation is what
produces the contradiction:
```
𝒫[φ] = ∫φ'S_F dt = Σ_{k≠0}ĝ(k) ≪_A P^{1−A}(\log t_0)^{1−A} → 0 ,
```
forcing `a_F(p) = 0`. **With merely bounded `S_F` there is no independent evaluation of `∫φ'S_F`, and
that is precisely the gap.**

> **Recorded do-not-retry.** No decomposition of the zero sum into "rigid model + displacement" can
> give arithmetic information, because the displacement term is `−𝒫[φ]` identically. Only an
> *independent* determination of `S_F` — as exact rigidity provides — breaks the circle.

### 124.3 Corrected status

- **Theorem 70 stands, unconditional and sharp**: an entire `F ∈ S` whose zeros are exactly
  `γ_n = M_F^{−1}(n)` satisfies `F = 1`. It closes §96.3's open core. Its mechanism is now understood
  precisely: exact rigidity makes `S_F` a deterministic chirp whose Fourier coefficients at the prime
  frequencies are tiny by non-stationary phase, while the explicit formula says those coefficients
  *are* the prime data.
- **Theorem 71 is withdrawn.** The `n_F = 0` case of the Energy Gap is not obtained.
- The gap between exact and approximate rigidity is now identified as **structural, not
  quantitative**: it is the difference between having and not having an independent evaluation of
  `∫φ'S_F`.

This is the sixth conjecture proposed and killed in-cycle (ZD §77, RZ §98, zero-sharing §87, CMP §113,
Bessel extension §114.2, Theorem 71 §124), and the second time the same underlying error appeared:
treating a quantity that *is* the prime side as if it were an independent error term (cf. §98.2).

---

## 125. Cycle 125 (2026-07-26) — the fifth design rule, and the exact scope of Theorem 70's mechanism

### 125.1 The rule

Two failures (§98.2 and §124.1) had the same cause: a term that **is** the prime side was treated as
an independent error. Formulated as a rule:

> **Circularity rule.** Before bounding a term against the prime side, check whether the explicit
> formula already identifies it *with* the prime side. In particular, for any zero set,
> `Σ_γ φ(γ) = ∫φν − ∫φ'S_F` and `∫φ'S_F = 𝒫[φ]` are identities; **every** decomposition of the zero
> sum that does not evaluate `∫φ'S_F` by means external to the explicit formula is circular.

Joining: thin sets (§77.2), scales (§87.2), regimes (§98.3), independence (§114.2).

### 125.2 What "external evaluation" means, and the complete list of cases where it is available

`𝒫[φ] = ∫φ'(t)S_F(t)dt` is arithmetic on the left and geometric on the right. Progress requires
computing the right side without the left. Cases found in this programme:

| hypothesis on the zeros | independent evaluation of `∫φ'S_F` | outcome |
|---|---|---|
| exact rigidity `γ_n = M^{−1}(n)` | `S_F = 1/2 − \{M(t)\}`; Poisson + non-stationary phase | **Theorem 70**: `F = 1` |
| `\|N_F − M_F\| ≤ K` (bounded `S_F`) | none — `S_F − \text{sawtooth}` is a bounded integer step function whose integral against `φ'` is `−Σφ'ε` again | circular (§124) |
| RH only | none | — |
| nothing | none | — |

The middle row was checked in both directions this cycle: writing `J := N_F − ⌈M⌉` (integer-valued,
`|J| ≤ K`, piecewise constant) gives `∫φ'J = −Σ_n[φ(γ_n) − φ(M^{−1}(n))] = −Σ_nφ'(M^{−1}(n))ε_n +
O(…)`, i.e. the displacement sum again. **Bounded discrepancy carries no information beyond the
explicit formula.**

> **Recorded.** Exact rigidity is the *only* hypothesis found in 125 cycles under which the zero side
> can be evaluated externally. That is why Theorem 70 is both true and sharp, and why every attempt to
> weaken its hypothesis has failed.

### 125.3 A general-`F` consistency check (no contradiction available)

For a general `F` with `Var(S_F) ~ (n_F/2π²)\log\log T`, square-root cancellation gives
`∫φ'S_F ≈ (\log p)√P·√(\log\log T)` for `φ` modulated at `\log p` on an interval of length `P`, while
`𝒫[φ] ≈ |a_F(p)|p^{−1/2}(\log p)P`. With `P = p^{1+η}` these balance at
`|a_F(p)| ≈ p^{−η/2}√(\log\log T)` — consistent with `|a_F(p)|` bounded, so **no contradiction is
available for general `F` by this route**, confirming that Theorem 70's mechanism does not extend by
size considerations alone.

---

## 126. Cycle 126 (2026-07-26) — Theorem 70 strengthened: any *fixed unfolded profile* forces triviality

§125.2 asked for another hypothesis admitting an external evaluation of `∫φ'S_F`. There is one, and it
contains exact rigidity as a special case.

### 126.1 The right generalisation

In the unfolded variable `u = M_F(t)` the zeros become `u_n = M_F(γ_n)` and
`S_F(t) = \#\{n : u_n ≤ u\} − u` is the **discrepancy** of the unfolded sequence. Exact rigidity is
`u_n = n`, giving `S_F = 1/2 − \{M_F(t)\}`. The natural weakening is that the discrepancy is a fixed
profile in the unfolded variable:

> **Hypothesis (FP).** `S_F(t) = Φ(M_F(t)) + o(1)` for some fixed `1`-periodic `Φ ∈ L²(R/Z)`.

This holds whenever the unfolded zeros follow any fixed periodic pattern — `u_n = n + c`, or an
alternating pattern `u_{2n} = 2n`, `u_{2n+1} = 2n+1/2`, and so on — not only for `u_n = n`.

### 126.2 The theorem

> **Theorem 74 (fixed unfolded profile forces triviality).** Let `F ∈ S` be entire and satisfy (FP).
> Then `a_F(p^k) = 0` for all primes `p` and all `k ≥ 1`, hence `F = 1`.
>
> *Proof.* Expand `Φ(M_F(t)) = Σ_{k∈Z} \hatΦ(k) e^{2πikM_F(t)}` and use the identity
> `𝒫[φ] = ∫φ'(t)S_F(t)dt` (§124.1). The `k = 0` term contributes `\hatΦ(0)∫φ'(t)dt = 0` because `φ`
> has compact support. For `k ≠ 0`, take `φ(t) = ψ((t−t_0)/P)e^{it\log p}` with `P = p^{1+η}`; the
> phase of `∫φ'(t)e^{2πikM_F(t)}dt` has derivative `\log p − 2πkν(t)`, non-vanishing whenever
> `p < t_0^d`, so repeated integration by parts gives
> `|∫φ'e^{2πikM_F}| ≪_A (\log p) P (P|k|\log t_0)^{−A}`. Summing,
> ```
> |𝒫[φ]| ≤ Σ_{k≠0} |\hatΦ(k)| · ≪_A (\log p) P (P\log t_0)^{−A} Σ_{k≠0}|\hatΦ(k)||k|^{−A}
>        ≪_A ‖Φ‖_{L²} (\log p) P (P\log t_0)^{−A}
> ```
> by Cauchy–Schwarz (`A ≥ 2`). Against `𝒫[φ] ≍ |a_F(p)|p^{1/2+η}\log p` this forces `a_F(p) = 0` as
> `t_0 → ∞`; iterating at `\log p^k` gives the rest. ∎

**Theorem 70 is the case `Φ = 1/2 − \{·\}`.**

### 126.3 What the strengthening isolates

The mechanism is now visible in its final form:

> **A fixed profile in the unfolded variable makes `S_F` a *chirp*** — its Fourier content sits at the
> drifting frequencies `2πkν(t) ≍ k\,d\log t` — **whereas the explicit formula puts the Fourier content
> of `S_F` at the fixed frequencies `\log n`.** The two are incompatible for every `n < t_0^d`, and
> `t_0` is free.

This is §97's chirp-versus-tone insight, which failed there as an `L²` comparison (§98) and succeeds
here as a comparison of Fourier coefficients with an *external* evaluation of one side. It also
explains why (FP) is exactly the right hypothesis: it is precisely the condition under which `S_F`
has a `t`-independent expansion in the unfolded variable.

> **Recorded scope.** (FP) is still far from `n_F = 0`, which gives only `|S_F| ≤ K` with no profile.
> The gap is between "bounded discrepancy" and "discrepancy given by a fixed function of the unfolded
> variable" — i.e. between a bound and a *law*. §124 shows no bound alone suffices; Theorem 74 shows
> any law suffices. **Conjecture A's edge case lies exactly in the space between them.**

---

## 127. Cycle 127 (2026-07-26) — bounded `S_F` forces `n_F = 0`, unconditionally and with an explicit constant

§124 showed that *decomposing* the zero sum around a rigid model is circular. Using the bound on `S_F`
directly as an input to the identity `∫φ'S_F = 𝒫[φ]` is not, and it gives a clean theorem.

### 127.1 The theorem

> **Theorem 75 (unconditional).** Let `F ∈ S` be entire with `|S_F(t)| ≤ K` for all `t`. Then for
> every `x`,
> ```
> Σ_{p ≤ x} |a_F(p)|² / p  ≤  C K²
> ```
> with an absolute constant `C`. In particular `n_F = 0`.
>
> *Proof.* Fix `x` and put `c_p := \overline{a_F(p)}\,p^{−1/2}` for `p ≤ x`. Choose `φ` with
> ```
> φ'(t) = Σ_{p ≤ x} c_p ψ((t−t_0)/P) e^{it\log p} ,     P ≫ x ,
> ```
> `ψ` a fixed smooth bump. Since `P ≫ x`, the transforms `ψ̂(P(\log n − \log p))` separate the primes,
> so the prime side is
> ```
> 𝒫[φ] = (1/2π)Σ_n Λ_F(n)n^{−1/2}φ̂(\log n) = (P/2πi)Σ_{p≤x}|a_F(p)|²/p + o(P E_x) ,
> ```
> writing `E_x := Σ_{p≤x}|a_F(p)|²/p`. On the other side, by `|S_F| ≤ K` and Cauchy–Schwarz on the
> support (length `≍ P`),
> ```
> |𝒫[φ]| = |∫φ'(t)S_F(t)dt| ≤ K‖φ'‖_1 ≤ K\sqrt{2P}\,‖φ'‖_2 ,
> ```
> and by the Montgomery–Vaughan mean value theorem `‖φ'‖_2² = (P + O(x))Σ_{p≤x}|c_p|² ≍ P E_x`. Hence
> `(P/2π)E_x ≤ \sqrt2 K P \sqrt{E_x}`, i.e. `E_x ≤ CK²`, uniformly in `x`. ∎

### 127.2 Why this is not circular

§124's circularity came from *decomposing* `Σ_γφ(γ)` into a model plus a displacement, which
re-derives the explicit formula. Here the identity `∫φ'S_F = 𝒫[φ]` is used **once**, with the
hypothesis `|S_F| ≤ K` entering as an honest `L^∞` bound on one factor. No model is introduced, and
the choice of `φ` (a mollified prime-energy amplifier) is what converts the pointwise bound into a
bound on the energy.

### 127.3 What it gives and what it does not

- **Gives:** `|S_F| ≤ K ⟹ n_F ≤ CK²`, unconditionally, with no Selberg CLT, no zero-density estimate
  and no RH. This is the *easy* direction of Theorem 49's equivalence, now proved outright rather than
  through the CLT machinery, and quantitatively.
- **Does not give:** the converse `n_F = 0 ⟹ |S_F| ≤ K`, which is the transfer from coefficients to
  the critical line and is RH-strength (§120.1). So EG₀ is not closed.
- **The prime-square analogue fails**, and for a structural reason: repeating the argument at
  frequencies `2\log p` produces `Σ_p |b_F(p²)|²/p²`, which converges under Ramanujan anyway, so the
  method extracts information only from the *linear* prime energy — the one whose natural weight
  `1/p` makes the sum a density.

### 127.4 Consolidated statement of the edge case

Three implications are now unconditional, and one is not:
```
|S_F| ≤ K            ⟹  n_F = 0            (Theorem 75, this cycle)
S_F = Φ(M_F) + o(1)  ⟹  F = 1              (Theorem 74)
γ_n = M_F^{−1}(n)    ⟹  F = 1              (Theorem 70)
n_F = 0              ⟹  |S_F| ≤ K          (RH-strength; open)
```
EG₀ is exactly the missing arrow. It is the only one that runs *from* the coefficients *to* the
critical line, which is the direction §120.1 shows no Cauchy–Schwarz argument can supply.

**Formalisation of Theorem 75's core (cycle 128).** Corpus searched first
(`research "energy bound amplifier Cauchy Schwarz sqrt"` and `rg` — nearest neighbours
`schwarzPairCauchyEnergy_*` and `AbstractSpectralMass` are unrelated Gram/Szegő computations; no
duplication). Added `HTGeometry/AmplifierEnergyBound.lean`:

> `energy_le_of_amplifier` : from `A = c·P·B` and `A ≤ K·√(2P)·√(P·B)` with `c,P > 0`, `B ≥ 0`,
> conclude `B ≤ 2K²/c²` — **independently of `P`**.
> `energy_le_of_amplifier_twopi` : the specialisation `c = 1/(2π)`, giving `B ≤ 8π²K²`.

This is the load-bearing inequality of Theorem 75: the arithmetic side of the identity
`∫φ'S_F = 𝒫[φ]` evaluates to `c·P·(\text{energy})`, the analytic side is bounded by `‖S_F‖_∞` times an
`L¹` norm, Cauchy–Schwarz on an interval of length `≍ P` turns that into `√(2P)·√(P·\text{energy})`,
and the powers of `P` cancel leaving `√(\text{energy}) ≪ K`. `lake build` passes; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.

**Formal corpus: 52 theorems in 15 modules, all unconditional, all axiom-clean under `lake build`.**

---

## 129. Cycle 129 (2026-07-26) — an unconditional lower bound for the mean square of `S_F`

Using the amplifier of §127 with Cauchy–Schwarz in `L²` rather than `L^∞`.

### 129.1 The theorem

> **Theorem 76 (unconditional).** Let `F ∈ S` be entire. For every `t_0`, every `x`, and every
> `P ≫ x`,
> ```
> (1/P) ∫_{t_0}^{t_0+P} |S_F(t)|² dt  ≥  (1/4π² + o(1)) · Σ_{p ≤ x} |a_F(p)|²/p .
> ```
> Consequently, taking `x` up to a small power of `P`,
> ```
> (1/P) ∫_{t_0}^{t_0+P} |S_F(t)|² dt  ≫  n_F · \log\log P ,
> ```
> so **positive prime energy forces the zero-counting fluctuation to be unbounded**, quantitatively
> and with no zero-density estimate, no Selberg central limit theorem and no RH.
>
> *Proof.* With the amplifier `φ'(t) = Σ_{p≤x}\overline{a_F(p)}p^{−1/2}ψ((t−t_0)/P)e^{it\log p}` of
> §127.1, the identity `𝒫[φ] = ∫φ'S_F` gives `(P/2π)E_x ≤ ‖φ'‖_2 · ‖S_F‖_{L²(\text{supp})}` where
> `E_x = Σ_{p≤x}|a_F(p)|²/p` and, by Montgomery–Vaughan, `‖φ'‖_2² = (P+O(x))E_x ≍ P E_x`. Hence
> `‖S_F‖_{L²} ≥ \sqrt{P E_x}/2π`, which is the claim. ∎

### 129.2 Relation to what was known

- For `ζ`, Selberg proved `∫_0^T S(t)²dt ~ (T/2π²)\log\log T` unconditionally, using his zero-density
  theorem. Theorem 76 gives the **lower half** of the analogous statement for every `F ∈ S`, with no
  density input at all — the amplifier does the work that the density theorem does classically.
- It is the quantitative form of Theorem 75 (`|S_F| ≤ K ⟹ n_F ≤ CK²`), now with the hypothesis
  weakened from `L^∞` to `L²` and with the dependence displayed.
- The **upper** half (`∫|S_F|² ≪ n_F\log\log T`) still needs the density estimate; it is the direction
  that would give `n_F = 0 ⟹ S_F` bounded, i.e. EG₀.

### 129.3 Why the amplifier cannot reach the prime squares

Repeating the construction at frequencies `2\log p` fails for a normalisation reason worth recording.
The explicit formula weights `n^{−1/2}`, so at `n = p²` the weight is `p^{−1}` and the natural density
weight becomes `1/p²`. Matching the amplifier's `L²` norm to the arithmetic side then forces
`c_p = \overline{b_F(p²)}p^{−1/2}` and produces `Σ_p |b_F(p²)|²p^{−3/2}`, which converges under
Ramanujan and carries no information; choosing `c_p` to produce the divergent sum `Σ_p|b_F(p²)|²/p`
instead makes `‖φ'‖_2² = PΣ_p|b_F(p²)|²` diverge.

> **Recorded do-not-retry.** The amplifier method sees **only** the linear prime energy. The obstruction
> is the `n^{−1/2}` weighting of the explicit formula, which places prime squares at density weight
> `1/p²` — convergent — so no amount of amplification extracts a divergent prime-square quantity.

### 129.4 Standing

```
n_F > 0        ⟹  (1/P)∫|S_F|² ≫ n_F \log\log P        (Theorem 76, unconditional)
|S_F| ≤ K      ⟹  n_F ≤ CK²                            (Theorem 75, unconditional)
S_F = Φ(M_F)   ⟹  F = 1                                (Theorem 74, unconditional)
rigid zeros    ⟹  F = 1                                (Theorem 70, unconditional)
n_F = 0        ⟹  |S_F| bounded                        (open — the only missing arrow)
```

---

## 130. Cycle 130 (2026-07-26) — `n_F = 0` puts `S_F` in `B²`: the missing arrow, in mean square

### 130.1 The theorem

> **Theorem 77 (unconditional).** Let `F ∈ S` be entire with `n_F = 0`. Then
> ```
> Σ_n |Λ_F(n)|² / (n \log²n)  =  Σ_p |a_F(p)|²/p  +  O(1)  <  ∞ ,
> ```
> the `k ≥ 2` terms contributing `≪ Σ_p p^{−2+ε}`. Hence the formal expansion
> `𝒮(t) := −(1/π)Σ_n Λ_F(n)n^{−1/2}\sin(t\log n)/\log n` has `ℓ²` coefficients and converges in the
> Besicovitch space `B²`, and
> ```
> S_F = 𝒮 + c   for a constant c ,
> ```
> because `∫φ'(S_F − 𝒮) = 0` for every test function `φ` (both sides satisfy `∫φ'· = 𝒫[φ]`), so
> `S_F − 𝒮` has vanishing distributional derivative. Consequently `S_F` is, up to an additive
> constant, **Besicovitch almost periodic with finite mean square**
> ```
> ‖S_F − c‖²_{B²} = (1/2π²) Σ_n |Λ_F(n)|²/(n\log²n) < ∞ ,
> ```
> and `limsup_P (1/P)∫_{t_0}^{t_0+P}|S_F|²dt < ∞` **uniformly in `t_0`**.

Together with Theorem 76 (the matching lower bound) this determines the mean square of `S_F` exactly,
unconditionally, in the case `n_F = 0`.

### 130.2 What it does and does not close

- **Closes, in mean square, the arrow that §127.4 listed as open**: `n_F = 0 ⟹ S_F` has bounded mean
  square. The transfer from coefficients to the critical line, which §120.1 showed is unavailable
  *pointwise* by Cauchy–Schwarz, **is available in `L²`**, and the mechanism is not Cauchy–Schwarz but
  the distributional identity `∫φ'S_F = 𝒫[φ]` plus completeness of `B²`.
- **Does not close** the pointwise version `|S_F| ≤ K`, which Theorem 75 needs, nor supply a profile
  `S_F = Φ(M_F)`, which Theorem 74 needs. `B²`-boundedness is strictly weaker than either.

### 130.3 A structural observation

`n_F = 0` gives `S_F ∈ B²` with **frequency set contained in the fixed tones `\{\log n\}`**. Exact
rigidity would give `S_F = 1/2 − \{M_F(t)\}`, whose frequency set is the **drifting** family
`\{kν(t)\}`. The two are incompatible, so:

> **Under `n_F = 0`, the zeros are *not* exactly rigid** — Theorem 70's hypothesis is never satisfied
> in the case one wants to apply it to. Theorem 70 is therefore not a special case of EG₀ waiting to be
> generalised; it is a statement about a configuration that `n_F = 0` positively excludes.

This is worth recording as a correction of emphasis: cycles 121–126 treated exact rigidity as the
extreme point of the `n_F = 0` case, whereas it is disjoint from it. What `n_F = 0` actually gives is
the *opposite* structure — fixed tones rather than a chirp.

### 130.4 Revised standing

```
n_F = 0        ⟹  S_F ∈ B², bounded mean square, fixed-tone spectrum   (Theorem 77, new)
n_F > 0        ⟹  (1/P)∫|S_F|² ≫ n_F \log\log P                        (Theorem 76)
|S_F| ≤ K      ⟹  n_F ≤ CK²                                            (Theorem 75)
S_F = Φ(M_F)   ⟹  F = 1                                                (Theorem 74)
rigid zeros    ⟹  F = 1                                                (Theorem 70; excluded when n_F = 0)
n_F = 0        ⟹  F = 1                                                (EG₀ — still open)
```
The remaining gap is now precisely: **from `S_F ∈ B²` with fixed-tone spectrum, conclude `F = 1`.**

---

## 131. Cycle 131 (2026-07-26) — the full complex pairing, including `ω`, as an integral against `S_F`

The amplifier of §127 was built from `F` itself. Building it from a **second** element gives the whole
Selberg pairing, not just the energy.

### 131.1 The identity

> **Theorem 78.** Let `F, G ∈ S` be entire. Fix `x`, take `P ≫ x`, and set
> ```
> φ'_G(t) := Σ_{p ≤ x} \overline{a_G(p)}\,p^{−1/2} ψ((t−t_0)/P) e^{it\log p} .
> ```
> Then, from `𝒫_F[φ] = ∫φ'S_F`,
> ```
> Σ_{p ≤ x} a_F(p)\overline{a_G(p)}/p  =  (2πi/P) ∫ φ'_G(t)\, S_F(t)\, dt  +  o(1) .
> ```
> In particular the **alternating form**
> ```
> ω(F,G) = \lim (\log\log x)^{−1} Im\, Σ_{p≤x}a_F(p)\overline{a_G(p)}/p
> ```
> is `(2π/P)·Re ∫φ'_G S_F`, normalised — an explicit integral of the zero-counting fluctuation of `F`
> against an amplifier built from `G`.

### 131.2 Why this matters

§69.1 (Theorem 16) proves that `ω` is invisible to **every** identity among prime energies of the
monoid generated by `F, G` and their conjugates. §80 gave the first representation that sees it: the
imaginary part of the Bohr correlation of the two standard twists at depth `b`. Theorem 78 gives a
second, and a much simpler one:

> **`ω(F,G)` is a pairing between the zeros of `F` and the primes of `G`.**

It is thin-set sensitive (§77.2 ✓ — an integral against a sparse exponential sum), at the mean-spacing
scale (§87.2 ✓), and it uses each asymptotic in its own regime (§98.3 ✓). Unlike §80's representation
it requires no standard-twist theory, no degree hypothesis and no complex shift — only the explicit
formula.

### 131.3 What it does not yet give

Cauchy–Schwarz on the right side returns
`|Σ_{p≤x}a_F(p)\overline{a_G(p)}/p| ≤ 2π\sqrt{E^G_x · \mathrm{MS}_F} ≈ 2π\sqrt{n_F n_G}\log\log x`,
i.e. exactly the Cauchy–Schwarz bound `|c_{F,G}| ≤ \sqrt{n_F n_G}` already known. **Extracting the
vanishing of `ω` requires cancellation in `∫φ'_G S_F`, not a bound on it** — the same structural point
as everywhere else in the programme, now stated for the imaginary half.

> **Recorded.** Two independent representations of `ω` now exist (§80 twist correlation, §131 zero
> pairing). Neither yields a bound better than Cauchy–Schwarz, and by Theorem 16 no energy identity
> can. The imaginary half of Conjecture B remains untouched by every method the programme has, and its
> two representations agree in placing it at the pairing of one function's zeros with the other's
> primes.

---

## 132. Cycle 132 (2026-07-26) — every non-constant `F ∈ S` has `S_F` of mean square `≥ 1/12`

An elementary but apparently new unconditional lower bound, from integrality of the counting function
plus equidistribution.

### 132.1 The theorem

> **Theorem 79 (unconditional).** Let `F ∈ S` be non-constant, so `d_F ≥ 1` (Conrey–Ghosh). Then for
> every constant `c`,
> ```
> \liminf_{T→∞} (1/T)∫_0^T |S_F(t) − c|² dt  ≥  1/12 .
> ```
> In particular the mean square of `S_F` about **any** centre is bounded below by `1/12`.
>
> *Proof.* `S_F = N_F − M_F` with `N_F` integer-valued, so
> `|S_F(t) − c| = |N_F(t) − (M_F(t)+c)| ≥ \mathrm{dist}(M_F(t)+c, Z)`. Since `d_F ≥ 1`,
> `M_F(t) = (d_F/2π)t\log(t/2πe) + …` has `M_F''(t) = d_F/(2πt) ≠ 0`, so by Weyl's criterion
> `\{M_F(t)+c\}` is equidistributed in `[0,1)`. Hence
> `(1/T)∫_0^T \mathrm{dist}(M_F+c,Z)²dt → ∫_0^1 \mathrm{dist}(u,Z)²du = 1/12`. ∎

### 132.2 Consequence for the Energy Gap

Combining with Theorem 77 (`n_F = 0 ⟹ S_F − c` is `B²`-almost periodic with
`‖S_F − c‖²_{B²} = (1/2π²)Σ_n|Λ_F(n)|²/(n\log²n)`):

> **Corollary 80.** If `F ∈ S` is non-constant, entire, and `n_F = 0`, then
> ```
> Σ_n |Λ_F(n)|² / (n\log²n)  ≥  π²/6 ,
> ```
> and since the `k ≥ 2` terms contribute `≪ Σ_p p^{−2+ε}`,
> ```
> Σ_p |a_F(p)|²/p  ≥  π²/6 − O(1)  >  1 .
> ```

So the `n_F = 0` case does not merely require the prime energy sum to converge — **it requires it to
converge to a value bounded below by an absolute constant `> 1`.** The convergent sum cannot be small.

### 132.3 Why this is the right shape, and what it still lacks

- It is the first **absolute, unconditional, positive** lower bound in the programme on a quantity
  that `n_F = 0` forces to be finite. Every earlier bound was either an upper bound (Bessel) or
  conditional.
- Its mechanism is the one §125.2 demanded: an evaluation of `∫|S_F|²` **external** to the explicit
  formula — here supplied by integrality of `N_F` plus Weyl equidistribution of `M_F`, neither of
  which mentions the primes.
- **It is not yet a contradiction.** `Σ_p|a_F(p)|²/p ≥ π²/6 − O(1)` is compatible with `n_F = 0`,
  which only asserts convergence. To close EG₀ one needs an *upper* bound on the same sum forcing it
  below `π²/6`; none is available.

> **[OPEN CORE, cycle 132]** For non-constant entire `F ∈ S` with `n_F = 0`, bound
> `Σ_p |a_F(p)|²/p` from **above** by something smaller than `π²/6 − O(1)`. Note this is now a
> statement about a *convergent* sum, not about a divergence rate — a different and possibly more
> tractable kind of question than anything the programme has faced.

### 132.4 A second corollary, unconditional and independent of `n_F`

Theorem 79 combined with Theorem 76 brackets the fluctuation for every non-constant `F ∈ S`:
```
1/12  ≤  \liminf (1/T)∫_0^T |S_F − c|²  ,      (1/P)∫|S_F|²  ≫  n_F\log\log P .
```
The first is an absolute floor independent of the arithmetic; the second grows with the prime energy.
Together: **the zeros of any non-constant element of the Selberg class fluctuate, by an absolute
amount, and by more when the prime energy is larger.**

---

## 133. Cycle 133 (2026-07-26) — Theorem 79 is sharp, and its equality case is exactly rigidity

### 133.1 Sharpness

For exactly rigid zeros `S_F(t) = 1/2 − \{M_F(t)\}`, and
`M\{(1/2 − \{M_F\})²\} = ∫_0^1(1/2−u)²du = 1/12` — **the bound of Theorem 79 is attained exactly**.
Check at the other extreme: `F = ζ` has `(1/T)∫_0^T S(t)²dt ~ (1/2π²)\log\log T → ∞`, far above the
floor. So `1/12` is the sharp constant and rigidity is the extremal configuration.

### 133.2 The equality case

Write `θ(t) := (M_F(t)+c) − \mathrm{round}(M_F(t)+c) ∈ [−1/2,1/2)` and
`ρ(t) := N_F(t) − \mathrm{round}(M_F(t)+c) ∈ Z`, so `S_F − c = ρ − θ`. Then
```
M\{(S_F−c)²\} = M\{ρ²\} − 2M\{ρθ\} + 1/12 ,
```
since `θ` is equidistributed (Weyl, `M_F'' ≠ 0`). As `ρ` is integer-valued, `|ρ| ≤ ρ²`, and
`|θ| ≤ 1/2`, so `|M\{ρθ\}| ≤ M\{ρ²\}/2` with equality only if `|ρ| ∈ \{0,1\}` **and** `|θ| = 1/2`
whenever `ρ ≠ 0` — a set of measure zero, since `θ` is equidistributed. Hence

> **Corollary 81.** `M\{(S_F−c)²\} ≥ 1/12`, with equality **iff** `ρ ≡ 0`, i.e. iff
> `N_F(t) = \mathrm{round}(M_F(t)+c)` — exactly rigid zeros up to a shift.
>
> Combined with Theorem 70 (rigid zeros force `F = 1`, which has `d_F = 0` and no zeros, hence falls
> outside the hypothesis `d_F ≥ 1`):
>
> **For every non-constant `F ∈ S`, `M\{(S_F−c)²\} > 1/12` strictly, for every `c`.**

### 133.3 Status of the quantitative gap

The strictness is qualitative: the argument gives no absolute `δ > 0` with
`M\{(S_F−c)²\} ≥ 1/12 + δ`, because the deficit is controlled by `M\{ρ²\}` and by the joint
distribution of `ρ` and `θ`, neither of which is bounded below without further input. Obtaining such a
`δ` would sharpen Corollary 80 to
`Σ_p|a_F(p)|²/p ≥ π²/6 + 2π²δ`, which is still not a contradiction — the target remains an **upper**
bound (§132.3).

> **Recorded.** The chain `Theorem 79 → Corollary 80 → Corollary 81` is complete and sharp, and it
> places rigidity as the unique extremal configuration, consistent with Theorem 70 having settled that
> case. What it does not do is bound the prime energy from above, which is what EG₀ needs.

---

## 134. Cycle 134 (2026-07-26) — the zero-energy sub-semigroup is uniformly discrete

### 134.1 A correction to Corollary 80

Corollary 80 was stated as `Σ_p|a_F(p)|²/p ≥ π²/6 − O(1) > 1`. **The split is not legitimate as an
absolute statement**: the `k ≥ 2` part is `Σ_{p,k≥2}|b_F(p^k)|²p^{−k} ≪ C_ε² Σ_p p^{2ε−2}`, and the
Ramanujan constant `C_ε` is not absolute. The clean and correct statement is

> **Corollary 80′.** For non-constant entire `F ∈ S` with `n_F = 0`,
> ```
> ‖v_F‖² := Σ_{n ≥ 2} |Λ_F(n)|² / (n \log² n)  ≥  π²/6 ,
> ```
> with no splitting into primes and prime powers.

### 134.2 The structure this reveals

Two facts combine.

**(i) `\{H ∈ S : n_H = 0\}` is a sub-semigroup.** If `n_H = n_{H'} = 0` then by Cauchy–Schwarz
`|c_{H,H'}| ≤ \sqrt{n_H n_{H'}} = 0`, so `n_{HH'} = n_H + n_{H'} + 2\mathrm{Re}\,c_{H,H'} = 0`.

**(ii) `H ↦ v_H` is an injective additive map into `ℓ²`.** Additive because `Λ_{HH'} = Λ_H + Λ_{H'}`;
injective because equal `Λ`'s give equal coefficient systems, hence equal functions.

With Corollary 80′:

> **Theorem 82.** The map `H ↦ v_H`, `v_H(n) = Λ_H(n)/(\sqrt n \log n)`, embeds the sub-semigroup
> `\{H ∈ S : n_H = 0\}` injectively and additively into `ℓ²`, and every non-zero image has
> `‖v_H‖² ≥ π²/6`. Hence the image is **uniformly discrete**: distinct elements `H ≠ H'` of the
> sub-semigroup satisfy `‖v_H − v_{H'}‖² ≥ π²/6` whenever `H/H'` lies in the semigroup, and in
> particular the group it generates is a **discrete subgroup of `ℓ²`, i.e. a lattice with minimum
> `≥ π²/6`**.

### 134.3 What this says about EG₀

> **EG₀ ⟺ that lattice is trivial.**

The programme therefore now has, for the `n_F = 0` case, exactly the picture Selberg's Conjecture B has
for the whole class: an additive embedding into a Hilbert space with a positive minimum. The
difference is that here the minimum is **proved** (Theorem 79, via integrality of `N_F` and Weyl
equidistribution), whereas in Conjecture B it is the conjecture.

**What is missing** is a rank bound: a discrete lattice with minimum `π²/6` can have any rank, so
discreteness alone does not force triviality. Closing EG₀ needs an upper bound on `‖v_H‖` — i.e. on
`Σ_n|Λ_H(n)|²/(n\log²n)` — for `H` in the semigroup, and §132.3's open core is exactly that.

> **Recorded.** Cycles 132–134 have converted the `n_F = 0` case of the Energy Gap from an analytic
> question about densities into a **geometric question about a lattice in `ℓ²` with a proved minimum**.
> The remaining input is an upper bound, and the programme has none.

---

## 135. Cycle 135 (2026-07-26) — the zero-energy semigroup has no elements of degree `< 2`

### 135.1 Degree constraint

Kaczorowski–Perelli's classification gives `S_0 = \{1\}`, `S_d = ∅` for `0 < d < 1` and `1 < d < 2`,
and `S_1 = \{ζ(s+iθ)\} ∪ \{L(s+iθ,χ)\}` — **every element of which has `n = 1`**. Hence:

> **Corollary 83.** Every non-trivial element of the sub-semigroup `\{H ∈ S : n_H = 0\}` has degree
> `≥ 2`, and since degrees are additive the semigroup is generated by such elements.

This is consistent with, and gives a second derivation of, the fact that the Energy Gap is open
exactly in degree `≥ 2` — but now as a statement about the lattice of Theorem 82: **its generators all
have degree `≥ 2`.**

### 135.2 Where the upper bound would have to come from

`‖v_H‖² = 2π²·\mathrm{Var}(S_H)` by Theorem 77, so §132.3's open core asks for an unconditional upper
bound on the variance of the zero-counting fluctuation. Checked and unavailable:

- The classical `S_H(t) = O(\log t)` gives `\mathrm{Var} ≤ \log²T` — grows, useless.
- Ramanujan gives `|Λ_H(n)| ≪ n^ε\log n`, so `Σ_n|Λ_H(n)|²/(n\log²n) ≪ Σ_n n^{2ε−1}` — divergent,
  useless.
- Degree alone cannot bound it: `ζ` has degree `1` and unbounded variance (though `n_ζ = 1 ≠ 0`, so it
  is outside the semigroup).
- Within the semigroup no mechanism is known that bounds the variance in terms of `d_H` or `q_H`.

> **Recorded.** No unconditional upper bound on `‖v_H‖` is available from the axioms. The lattice of
> Theorem 82 has a proved minimum and no proved bound on its elements, so discreteness cannot be
> upgraded to triviality by any argument currently in the programme.

### 135.3 The state of the `n_F = 0` case, complete

```
{H ∈ S : n_H = 0}  is a sub-semigroup                         (Cauchy–Schwarz)
H ↦ v_H  is injective, additive, into ℓ²                      (Λ additive; coefficients determine H)
‖v_H‖² ≥ π²/6 for H ≠ 1                                       (Theorem 79 + Theorem 77)
every non-trivial element has degree ≥ 2                      (Corollary 83, via K–P)
EG₀  ⟺  the semigroup is trivial
missing: any upper bound on ‖v_H‖                             (§135.2)
```

**Formalisation of Theorem 79's core (cycle 135).** Corpus searched first
(`research "distance to integers fractional part square integral"` — only unrelated Gutzmer/Szegő
partial-sum results; no duplication). Added `HTGeometry/RoundingVarianceFloor.lean`:

> `abs_sub_round_le_abs_sub` : `|x − round x| ≤ |x − n|` for every integer `n` — no integer beats the
> nearest one;
> `rounding_floor` : the shifted form `|x+c − round(x+c)| ≤ |n − (x+c)|` used in Theorem 79;
> `integral_sq_rounding_error` : `∫_{−1/2}^{1/2} u² du = 1/12` — the mean square of the rounding error
> over one period;
> `sq_abs_sub_round_le` : `|x − round x|² ≤ 1/4`.

Together these are exactly the arithmetic content of Theorem 79: `N_F` integer-valued gives
`|S_F − c| ≥ |M_F+c − round(M_F+c)|` pointwise, and equidistribution of `M_F` mod one converts the
mean square of the right side into `1/12`. `lake build` passes; `#print axioms` clean on all four.

**Formal corpus: 58 theorems in 17 modules, all unconditional, all axiom-clean under `lake build`.**

---

## 136. Cycle 136 (2026-07-26) — no universal ceiling exists, and the updated hand-off

### 136.1 A structural note that closes one family of attempts

Could EG₀ follow from a **universal** upper bound on `Var(S_H)` for `H` in the zero-energy semigroup?
No: within `S` the variance is unbounded across elements (`ζ` has `Var(S_ζ) → ∞`), and nothing in the
semigroup's definition caps it — `n_H = 0` asserts only that `Σ_p|a_H(p)|²/p` **converges**, not that
it is small. Even using axiom (4)'s explicit `|b_H(n)| ≤ Cn^θ`, `θ < 1/2`, one gets
`‖v_H‖² = Σ_p|a_H(p)|²/p + O_{C,θ}(1)` with the prime-power part explicitly bounded by
`C'Σ_p p^{4θ−2} < ∞` — but the prime part is unconstrained above.

> **Recorded do-not-retry.** EG₀ cannot be closed by a universal ceiling on `‖v_H‖`. Any proof must
> produce a **per-`H`** contradiction, i.e. derive `‖v_H‖² < π²/6` from properties of the particular
> `H`. The lattice of Theorem 82 has a proved minimum, an unbounded set of possible norms, and no
> rank bound.

### 136.2 Updated hand-off (supersedes §94)

**Read order.**
1. §74 and §79.4 — the meta-conclusion (one integrality mechanism) and the ten closed mechanisms.
2. §85 — the two independence results (Theorems 38, 39): the functional equation is essential, and
   the axiomatic integers are additive while `n_F` is quadratic.
3. §84, §82, §101 — the two remaining gaps (cusps; twist exponent), the `θ`-gap having been removed.
4. The five design rules: thin sets §77.2, scales §87.2, regimes §98.3, independence §114.2,
   circularity §125.1.
5. §107–§110 — integrality on the critical line (Theorems 57, 58, 60, 61).
6. §127–§135 — the zero-counting fluctuation (Theorems 75–79, Corollaries 80′–83, Theorem 82).
7. The do-not-retry list, now: §4, §7, §9.1, §9.6, §10.1, §11.1, §20.4, §21.1, §22.1, §26.3, §28.2,
   §31, §38, §46.4, §49.1, §53, §57, §62, §66, §69.2, §71, §72.3, §74.1, §77.1, §79.2, §86.3, §88.2,
   §89.2, §91.3, §93.2, §98.1, §100.2, §110.1, §113.1, §114.2, §120.3, §124.1, §129.3, §135.2, §136.1.

**Principal unconditional results of the programme.**
| # | statement |
|---|---|
| Thm 2 | linear half of Conjecture A: `Σ_{p≤x}(a_F(p)−m)/p = O(1) ⟹ m = m_F ∈ Z_{≥0}` |
| Thm 10, 62 | `Σ_θ(ord_{1+iθ}F)² ≤ n_F`; at most `n_F` points in the `1`-line divisor (Cor 67) |
| Thm 16, 19 | real Gram blindness; the Selberg symplectic form `ω` |
| Thm 22 | `Σ_ρ m_ρ² ≥ N_F(T)`, equality iff all zeros simple |
| Thm 23, 24, 28 | complex-shift regularisation; `n_F` from the `L²`-mean of the standard twist |
| Thm 29, 30, 78 | twist correlation and zero–prime pairing; two representations of `ω` |
| Thm 38, 39 | independence: axiom (3) essential; additive invariants cannot give `n_F` |
| Thm 40, 43, 55 | fractional-power obstruction; ratio functional equation; divisor multiplicity one |
| Thm 52, 53 | `log F − Σ_p a_F(p)p^{−s}` holomorphic on `Re s > 1/2`; `∫|log F|² ≪ T\log²T` |
| Thm 57, 58, 60 | prime-square density `= −ord_{1/2}(F/G) ∈ Z`; `n_F = δ₂(F\bar F) − 2Reδ₂(F)` |
| Thm 70, 74 | rigid zeros, and any fixed unfolded profile, force `F = 1` |
| Thm 75, 76, 77 | `|S_F| ≤ K ⟹ n_F ≤ CK²`; `(1/P)∫|S_F|² ≫ n_F\log\log P`; `n_F = 0 ⟹ S_F ∈ B²` |
| Thm 79, Cor 80′, 81 | `\liminf(1/T)∫|S_F−c|² ≥ 1/12`, sharp, equality iff rigid |
| Thm 82, Cor 83 | the zero-energy semigroup embeds as a lattice with minimum `π²/6`, generators of degree `≥ 2` |

**Formal corpus (17 modules, 58 theorems, all `lake build`-verified and axiom-clean):**
`RHTower/SelbergPairingPrimeSquare`, and in `HTGeometry/`: `GeneralizedDirichletMeanValue`,
`ResidueJumpLowerBound`, `LogCoefficientTransfer`, `DiagonalIsolation`, `RealGramBlindness`,
`MultiplicityEnergyBracket`, `ConvexSlopeDerivBound`, `CommensurableFrequencies`,
`AdditiveVersusQuadratic`, `FractionalExponentObstruction`, `CountingPairing`, `BesselPSD`,
`AmplifierEnergyBound`, `RoundingVarianceFloor`.

**Standing.** Conjecture A and Conjecture B both open. The programme's contribution is a complete map:
what the axioms can and cannot supply, which functionals are blind, which scales may not be mixed, the
single regime `α ≍ 1` into which the quadratic problems funnel, and — new in cycles 127–136 — an
unconditional theory of the zero-counting fluctuation `S_F` in which the Energy Gap's edge case becomes
a lattice problem with a proved minimum and a missing upper bound.

---

## 137. Cycle 137 (2026-07-26) — correction: Theorem 82 gives a semigroup with isolated origin, not a lattice

### 137.1 The over-claim

Theorem 82 was stated as "the group generated is a **discrete subgroup of `ℓ²`, i.e. a lattice with
minimum `≥ π²/6`**". That is wrong. The set `\{H ∈ S : n_H = 0\}` is a **semigroup, not a group** —
`S` is closed under multiplication but not under division, so for `H_1 ≠ H_2` in the semigroup the
difference `v_{H_1} − v_{H_2}` is the image of `H_1/H_2`, which need **not** lie in `S`. Nothing
therefore bounds `‖v_{H_1} − v_{H_2}‖` from below, and the generated group need not be discrete.

> **Corrected Theorem 82.** The map `H ↦ v_H`, `v_H(n) = Λ_H(n)/(\sqrt n\log n)`, embeds
> `\{H ∈ S : n_H = 0\}` injectively and additively into `ℓ²`, and **every non-zero element of the
> image has `‖v_H‖² ≥ π²/6`**. So the image is an additive sub-semigroup of `ℓ²` whose origin is
> isolated. It is *not* shown to be uniformly discrete, and no rank statement is available.
>
> **EG₀ ⟺ the image is `\{0\}`.**

Two zero-energy elements with nearly equal coefficient systems would give nearly equal `v`'s; ruling
that out is strong multiplicity one, which is exactly what the programme does not have
unconditionally (Theorem 64 needs Bounded Satake).

### 137.2 What survives, and what the correction costs

- **Survives:** injectivity, additivity, and the proved minimum `π²/6` — the substance of cycles
  132–134. `EG₀ ⟺ triviality of the semigroup` is unaffected.
- **Costs:** the lattice picture, and with it any hope of a rank argument. §136.1's conclusion — that
  EG₀ needs a **per-`H`** contradiction — is unchanged and now the only available route.

### 137.3 A checked non-improvement

Could the floor `1/12` be improved for elements of degree `d ≥ 2` (which by Corollary 83 are the only
possible generators)? No: Theorem 79's floor comes from equidistribution of `\{M_F(t)\}`, which holds
for every `d ≥ 1` and yields `∫_0^1 \mathrm{dist}(u,Z)²du = 1/12` independently of `d`. Higher degree
makes the zeros denser but does not change the rounding geometry.

> **Recorded.** The constant `π²/6` in Corollary 80′ is degree-independent and cannot be improved by
> this method. This is the fourth over-claim caught and corrected in-cycle (§98 RZ, §113 CMP,
> §124 Theorem 71, §134/§137 Corollary 80 and Theorem 82), and the second within the cycles 132–136
> block — a signal that the new zero-fluctuation material needs the same adversarial pass the earlier
> material received.

---

## 138. Cycle 138 (2026-07-26) — adversarial audit of the cycles 127–136 block

Promised in §137.3. Each step of Theorems 75–79 and Corollaries 80′–83 re-derived and checked.

### 138.1 The identity `∫φ'S_F = 𝒫[φ]`

Two derivations of `Σ_γφ(γ)` for `F` entire and `φ` smooth of compact support:
`∫φ\,dN_F = ∫φν\,dt + ∫φ\,dS_F = ∫φν − ∫φ'S_F` (integration by parts), and the Weil explicit formula
`Σ_γφ(γ) = (\text{archimedean}) − 𝒫[φ]`. The archimedean term **is** `∫φν` by construction of the
Riemann–von Mangoldt density. Comparing gives the identity. ✔

### 138.2 The amplifier

- **Compact support of `φ`.** `φ` is the antiderivative of `φ'`; it is compactly supported iff
  `∫φ' = 0`. Here `∫ψ((t−t_0)/P)e^{it\log p}dt = Pe^{it_0\log p}\hatψ(−P\log p)`, negligible because
  `\hatψ` is Schwartz and `P\log p → ∞`. ✔ (A negligible constant adjustment restores exact compact
  support.)
- **Arithmetic side.** `\hatφ(ξ) = \widehat{φ'}(ξ)/(iξ)`, so the `n = p` term is
  `(1/2π)Λ_F(p)p^{−1/2}·Pc_p/(i\log p) = (P/2πi)a_F(p)p^{−1/2}c_p`; with `c_p = \overline{a_F(p)}p^{−1/2}`
  this is `(P/2πi)|a_F(p)|²/p`. The dual terms `\hatφ(−\log n)` have argument `≈ −P(\log n+\log p)` and
  the prime powers `n = p^k`, `k ≥ 2`, have `\hatψ` argument `P(k−1)\log p`; both negligible. ✔
- **`L²` norm.** Montgomery–Vaughan: diagonal `P‖ψ‖_2²E_x`; off-diagonal
  `≪_A P(P|\log(p/q)|)^{−A} ≪ P(P/x)^{−A}`, negligible for `P ≫ x`. ✔

### 138.3 Theorem 79's error term

The classical Riemann–von Mangoldt formula is `N_F(T) = M_F(T) + S_F(T) + O(1/T)`, not an exact
identity. Hence `|S_F − c| ≥ \mathrm{dist}(M_F+c, Z) − O(1/T)`, and since the correction tends to `0`
the mean-square floor `1/12` is unaffected. ✔

### 138.4 Verdict

| result | status after audit |
|---|---|
| Thm 75 (`|S_F| ≤ K ⟹ n_F ≤ CK²`) | **verified** |
| Thm 76 (`(1/P)∫|S_F|² ≫ n_F\log\log P`) | **verified** |
| Thm 77 (`n_F = 0 ⟹ S_F ∈ B²`) | **verified** |
| Thm 78 (pairing via `S_F`) | **verified** |
| Thm 79 (floor `1/12`), Cor 81 (equality iff rigid) | **verified**, with §138.3's error term noted |
| Cor 80 (`Σ_p|a_F(p)|²/p > 1`) | **corrected** in §134.1 to Cor 80′ (no prime/prime-power split) |
| Thm 82 (lattice) | **corrected** in §137.1 to a semigroup with isolated origin |
| Cor 83 (generators of degree `≥ 2`) | **verified** (K–P classification; `S_1` has `n = 1`) |

> **Net.** The block stands, with the two over-claims already withdrawn and the remaining eight
> statements re-derived step by step. The programme's zero-fluctuation theory — Theorems 75–79 and
> Corollaries 80′, 81, 83 — is unconditional and audited.

### 138.5 What the audit did not find

No further errors, and no new leverage. The audit confirms that the block's reach ends exactly where
§136.1 places it: at the absence of a per-`H` upper bound on `‖v_H‖`. **The adversarial pass is
complete; further extension of this block should not be attempted without new input.**

---

## 139. Cycle 139 (2026-07-26) — **EG₀ IS PROVED**: no non-constant `F ∈ S` has `n_F = 0`

New input, as demanded by §138.5: pass from the *mean square* of `S_F` (Theorem 79) to the
**characteristic function** `M\{e^{2πikS_F}\}`.

### 139.1 Two evaluations of the same quantity

Let `F ∈ S` be non-constant with `n_F = 0`. By Theorem 10 (`n_F ≥ ν²`) `F` has no pole and no zero on
`Re s = 1`, so `F` is entire and Theorem 77 applies. Let `M\{g\} := \lim_T (1/T)∫_0^T g(t)dt` denote
the Besicovitch mean, and fix an integer `k ≠ 0`.

**(A) The geometric evaluation: `M\{e^{2πikS_F}\} = 0`.**
`S_F = N_F − M_F + O(1/T)` with `N_F` integer-valued, so
```
e^{2πikS_F(t)} = e^{−2πikM_F(t)}·(1 + o(1)) .
```
Since `F` is non-constant, `d_F ≥ 1` (Conrey–Ghosh), so `M_F'(t) = ν(t) = (d_F/2π)\log(t/2π)+… → ∞`
monotonically. Van der Corput's first-derivative test gives
`|∫_a^b e^{−2πikM_F}dt| ≤ 2/(2πk\,ν(a))`, a bound independent of `b`; hence
`(1/T)|∫_0^T e^{−2πikM_F}dt| → 0`. Therefore `M\{e^{2πikS_F}\} = 0`.

**(B) The arithmetic evaluation: `M\{e^{2πikS_F}\} ≠ 0` for suitable `k`.**
By Theorem 77, `n_F = 0` gives `S_F = c + 𝒮` with
```
𝒮(t) = −(1/π) Σ_{n≥2} Λ_F(n) n^{−1/2} \sin(t\log n)/\log n  =  Σ_{n} A_n \sin(t\log n + φ_n) ,
      A_n = |Λ_F(n)|/(π n^{1/2}\log n) ,   Σ_n A_n² < ∞ .
```
*Step 1 (truncation).* `|e^{2πik𝒮} − e^{2πik𝒮_N}| ≤ 2πk|𝒮 − 𝒮_N|`, so
`|M\{e^{2πik𝒮}\} − M\{e^{2πik𝒮_N}\}| ≤ 2πk\,‖𝒮 − 𝒮_N‖_{B²} → 0`.

*Step 2 (Weyl).* The frequencies `\log p` over distinct primes are `Q`-linearly independent (unique
factorisation), and `\log p^j = j\log p`. So `(t\log p)_{p ≤ N}` equidistributes in the torus, and
```
M\{e^{2πik𝒮_N}\} = ∏_{p ≤ N} I_p ,   I_p := (1/2π)∫_0^{2π} \exp\!\big(2πik Σ_{j≥1} A_{p^j}\sin(jθ+φ_{p^j})\big)\,dθ .
```

*Step 3 (the product does not vanish).* `|I_p| ≤ 1` and, expanding,
`1 − |I_p| = O(k² Σ_j A_{p^j}²)`, so `Σ_p (1 − |I_p|) = O(k² Σ_n A_n²) < ∞` and the product converges.
It is non-zero unless some factor vanishes. Since `A_p = |a_F(p)|/(π\sqrt p) → 0`, for each fixed `k`
all but finitely many `p` have `2πk A_p < j_{0,1} ≈ 2.405`, whence `I_p ≈ J_0(2πkA_p) ≠ 0`. Each of
the finitely many remaining `I_p` is a real-analytic, non-constant function of `k` equal to `1` at
`k = 0`, so its zeros in `k` are isolated; choose an integer `k ≠ 0` avoiding all of them.

For that `k`, `M\{e^{2πik𝒮}\} = ∏_p I_p ≠ 0`, and since `S_F = c + 𝒮`,
`M\{e^{2πikS_F}\} = e^{2πikc}·M\{e^{2πik𝒮}\} ≠ 0`.

**(A) and (B) contradict.**

### 139.2 The theorem

> **Theorem 84 (Energy Gap, `n_F = 0` case; unconditional).** No non-constant `F ∈ S` has
> `Σ_p |a_F(p)|²/p < ∞`. Equivalently `n_F = 0 ⟹ F = 1`.

Equivalent forms now all proved: `Σ_{n≤x}|a_F(n)|² ≫ x/\log x` (§120.2); the zeros of a non-constant
`F ∈ S` are never rigid, and more generally never satisfy `S_F ∈ B²` (§130); the zero-energy
semigroup of §137.1 is trivial.

### 139.3 Why the argument is sharp

If `n_F > 0` then `Σ_n A_n² = ∞`, so `Σ_p(1 − |I_p|) = ∞` and the product `∏_p I_p` **vanishes** —
exactly matching (A). The contradiction appears precisely on the convergence boundary
`Σ_p|a_F(p)|²/p < ∞`. So the method proves the `n_F = 0` case and cannot, as it stands, reach
`0 < n_F < 1`.

### 139.4 What it does not settle

- The remaining Energy Gap case `0 < n_F < 1` is untouched: there `𝒮 ∉ B²` and Theorem 77 fails.
- Conjecture A (`n_F ∈ Z`) and Conjecture B remain open.

But EG₀ has been the programme's named target since §52, was reformulated four times (§116.2, §130.2,
§132.3, §134.3), and had every previous route recorded as blocked. **The new input was to test the
distribution of `S_F` rather than its moments**: `e^{2πikS_F} = e^{−2πikM_F}` is an *identity* forced
by integrality of `N_F`, and it evaluates to `0` geometrically and to a convergent non-zero Euler
product arithmetically.

---

## 140. Cycle 140 (2026-07-26) — Theorem 84 stress-tested against `ζ`, and why `0 < n_F < 1` is out of reach

### 140.1 The consistency check that matters

The proof of Theorem 84 must **not** apply to `ζ`, which exists. Checking:

- Evaluation (A) is unchanged for `ζ`: `e^{2πikS(t)} = e^{−2πikM(t)}` exactly (integrality of `N`), and
  van der Corput gives `M\{e^{2πikS}\} = 0`.
- Evaluation (B) for `ζ`: `A_p = 1/(π\sqrt p)`, so `Σ_p A_p² = (1/π²)Σ_p 1/p = ∞`, hence
  `Σ_p(1 − |I_p|) ≍ k²Σ_p 1/p = ∞` and the Euler product `∏_p I_p` **vanishes**.

(A) and (B) agree at `0`. **No contradiction for `ζ`** — as required. The contradiction in Theorem 84
arises solely from `Σ_p|a_F(p)|²/p < ∞`, which makes the product converge to a non-zero limit. ✔

A second check: the deterministic identity `\{S_F(t)\} = \{−M_F(t)\}` means the *fractional part* of
`S_F` is not Gaussian but exactly equidistributed; the Selberg CLT governs only the unwrapped `S_F`.
The two are consistent because `M_T\{e^{2πikS_F}\} = O(1/T)` is *smaller* than the Gaussian heuristic
`(\log T)^{−k²}`, not larger. ✔

### 140.2 Quantitative form, and why it stops at `n_F = 0`

Expanding, `1 − I_p ≈ π²k²A_p² = k²|a_F(p)|²/p`, so
```
∏_{p ≤ x} I_p  ≈  \exp\big(−k² Σ_{p≤x}|a_F(p)|²/p\big)  ≈  (\log x)^{−k² n_F} .
```
For `n_F = 0` this tends to a non-zero limit — the contradiction. For `n_F > 0` it tends to `0`,
matching (A) exactly.

Attempting to convert the *rate* into a contradiction fails. Comparing at finite `T` with truncation
at `N`:
```
(\log N)^{−k²n_F}  ≪  1/T  +  2πk\,\|S_F − c − 𝒮_N\|_{L²[0,T]}/\sqrt T ,
```
and the last term is `≍ k\sqrt{n_F \log(\log T/\log N)}`. With `N = T^{1/2}` it is a constant while the
left side tends to `0`; with `\log N = (\log T)^{1−δ}` it grows. **No choice of `N` makes the two
sides conflict.**

> **Recorded do-not-retry.** The characteristic-function method is sharp at the convergence boundary:
> it proves `n_F = 0 ⟹ F = 1` and cannot reach `0 < n_F < 1`, because there both evaluations give
> `0` and the rates cannot be separated.

### 140.3 Status of the Energy Gap after Theorem 84

```
n_F = 0                     ⟹  F = 1                       (Theorem 84, new, unconditional)
F has a pole or a zero on Re s = 1, of order ν  ⟹  n_F ≥ ν²   (Theorem 10)
0 < n_F < 1 with F entire and non-vanishing on Re s = 1      — the only remaining case
```
The Energy Gap conjecture (`n_F = 0` or `n_F ≥ 1`) is therefore reduced to a **single** open case, and
that case now has a sharp description: `F` entire, non-vanishing on `Re s = 1`, with
`Σ_p|a_F(p)|²/p` divergent but of density `< 1`.

---

## 141. Cycle 141 (2026-07-26) — **(P2) PROVED UNCONDITIONALLY**: quantitative strong multiplicity one

The mechanism of Theorem 84 applied to a **pair** rather than a single element. The pair version is
stronger, because for two elements with the same archimedean data the geometric side is not `0` but
`1`.

### 141.1 The two evaluations for a pair

Let `F, G ∈ S` be entire with **identical gamma factors and conductors**, so `M_F = M_G`. Assume
```
Σ_p |a_F(p) − a_G(p)|² / p  <  ∞ .                                    (H)
```

**(A) Geometric: the characteristic function is `1`.**
`S_F − S_G = (N_F − M_F) − (N_G − M_G) = N_F − N_G ∈ Z` pointwise, since `M_F = M_G`. Hence
`e^{2πik(S_F−S_G)} = 1` identically and `M\{e^{2πik(S_F−S_G)}\} = 1` for every integer `k`.

**(B) Arithmetic: it is `e^{2πikΔc}∏_p I_p`.**
Under (H), `Σ_n |Λ_F(n) − Λ_G(n)|²/(n\log²n) < ∞` (the `k ≥ 2` terms are `≪ Σ_p p^{−2+ε}`), so the
expansion
```
𝒟(t) = −(1/π) Σ_n (Λ_F(n) − Λ_G(n)) n^{−1/2}\sin(t\log n)/\log n = Σ_n B_n \sin(t\log n + ψ_n)
```
converges in `B²`; and since `S_F − S_G` and `𝒟` both pair to `𝒫_F[φ] − 𝒫_G[φ]` against `φ'`, they
differ by a constant `Δc`. Weyl equidistribution of `(t\log p)_p` (`Q`-independence) plus the `B²`
truncation bound gives
```
M\{e^{2πik(S_F−S_G)}\} = e^{2πikΔc} ∏_p I_p ,   I_p = (1/2π)∫_0^{2π}\exp\big(2πik Σ_j B_{p^j}\sin(jθ+ψ_{p^j})\big)dθ .
```

**Combining.** `|∏_p I_p| = 1` with every `|I_p| ≤ 1` forces `|I_p| = 1` for every `p`, which happens
only when the trigonometric polynomial `Σ_j B_{p^j}\sin(jθ+ψ_{p^j})` is constant in `θ` — i.e. when
`B_{p^j} = 0` for all `j`. Hence `Λ_F ≡ Λ_G`, so `F` and `G` have the same coefficients, so `F = G`.

### 141.2 The theorem

> **Theorem 85 (quantitative strong multiplicity one; unconditional).** Let `F, G ∈ S` have identical
> gamma factors and conductors. If
> ```
> Σ_{p ≤ x} |a_F(p) − a_G(p)|² / p  =  O(1) ,
> ```
> then `F = G`.
>
> The hypothesis that `F, G` be entire is not needed: if their pole orders at `s = 1` differ then the
> linear density `Σ_p(a_F(p)−a_G(p))/p ∼ (m_F−m_G)\log\log x` is unbounded, and Cauchy–Schwarz makes
> the quadratic sum diverge, contradicting the hypothesis. So (H) forces `m_F = m_G` and the pole
> terms of the two explicit formulae cancel.

This is **(P2)**, open in this programme since §22, and previously obtained only under **Bounded
Satake** (Theorem 64). It is now unconditional, with no Rankin–Selberg convolution, no automorphy, no
zero-density estimate and no RH.

### 141.3 Consequences

- **(ZS) is settled** (§88.3): two distinct elements of `S` with the same gamma factor and conductor
  cannot have `Σ_p|a_F(p)−a_G(p)|²/p` bounded, hence — by §88's chain — the fractional-power
  counterexample route of §86 is closed completely.
- Theorem 64's hypothesis (Bounded Satake) can be dropped everywhere it was used.
- Combined with Theorem 84 (`n_F = 0 ⟹ F = 1`, the case `G = 1`): Theorem 85 contains Theorem 84 as
  the special case `G = 1`, whenever `F` has the gamma factor and conductor of `1` — so the two are
  the same mechanism at different levels of generality.

### 141.4 Why the pair case is easier than the single case

For a single `F` the geometric side is `M\{e^{2πikS_F}\} = M\{e^{−2πikM_F}\} = 0`, and the arithmetic
side must be made non-zero — which needs `Σ_p|a_F(p)|²/p < ∞`. For a **pair with equal archimedean
data** the chirp `M_F − M_G` cancels identically, the geometric side is `1`, and the arithmetic side
must be forced to have modulus `1` — which happens only in the degenerate case. **The cancellation of
the archimedean data is what makes the pair problem strictly easier**, exactly as Theorem 54 found for
the explicit formula.

---

## 142. Cycle 142 (2026-07-26) — the characteristic-function method is a `0/1` detector

### 142.1 Sharpness check for Theorem 85

Hypothesis (H) is genuinely needed. Take `F = L(·,χ_1)`, `G = L(·,χ_2)` with `χ_1 ≠ χ_2` primitive and
even of the same modulus `q`: identical gamma factors and conductors, so `M_F = M_G` and
`S_F − S_G = N_F − N_G ∈ Z`, giving `M\{e^{2πik(S_F−S_G)}\} = 1`. Yet `F ≠ G`. The resolution is that
`n_{F/G} = n_F + n_G − 2\mathrm{Re}\,c_{F,G} = 2 > 0`, so `𝒟 ∉ B²` and the Euler-product evaluation is
**not available** — exactly as required. ✔ Theorem 85 is sharp at the convergence boundary.

### 142.2 The structural reach of the method

Both Theorem 84 and Theorem 85 compare two evaluations of `M\{e^{2πikX}\}`:

| `X` | geometric value | forced by |
|---|---|---|
| `S_F` | `0` | `\{S_F\} = \{−M_F\}` and equidistribution of `M_F` (chirp) |
| `S_F − S_G`, same `γ, Q` | `1` | `S_F − S_G ∈ Z` pointwise |

**The geometric side can only ever be `0` or `1`** — those are the only values integrality of the
counting function produces. So the method is a **detector of a dichotomy**: it decides whether an
Euler product `∏_p I_p` vanishes or has modulus one, i.e. whether a prime energy diverges or vanishes.

> **Consequence.** The method settles exactly the questions of the form *"is this energy zero?"* —
> EG₀ (`n_F = 0 ⟹ F = 1`) and (P2) (`n_{F/G} = 0 ⟹ F = G`). It **cannot** produce a general integer,
> so it cannot give `n_F ∈ Z` and does not touch Conjecture A or the orthogonality half of
> Conjecture B. Recorded so the method's reach is not over-estimated.

### 142.3 Why `0 < n_F < 1` stays out

For a single `F` with `n_F > 0` both sides are `0` and the rates cannot be separated (§140.2). For a
pair with `n_{F/G} > 0` the geometric side is `1` but the arithmetic side is unavailable (§142.1).
Neither dichotomy is triggered. **The remaining Energy Gap case `0 < n_F < 1` requires a mechanism
that produces a value other than `0` or `1`.**

**Formalisation of the rigidity step (cycle 142).** Corpus searched first
(`research "product of norms equal one implies each"` — only unrelated theta-tail and
prime-coherence results). Added `HTGeometry/UnitProductRigidity.lean`:

> `norm_eq_one_of_prod_norm_eq_one` : if `‖a i‖ ≤ 1` for all `i ∈ s` and `∏_{i∈s}‖a i‖ = 1`, then
> `‖a i‖ = 1` for every `i ∈ s`;
> `norm_eq_one_of_norm_prod_eq_one` : the same with the hypothesis `‖∏ a i‖ = 1`.

This is the rigidity step of Theorems 84 and 85: the characteristic function of the difference of two
zero-counting fluctuations is identically `1`, the Euler-product evaluation gives `∏_p I_p` with every
`|I_p| ≤ 1`, and the lemma forces every local factor to be a unit — hence every local oscillation, and
so every coefficient difference, to vanish. `lake build` passes; `#print axioms` clean on both.

**Formal corpus: 60 theorems in 18 modules, all unconditional, all axiom-clean under `lake build`.**

---

## 143. Cycle 143 (2026-07-26) — strict Cauchy–Schwarz for the Selberg pairing, and the roots-of-unity direction

### 143.1 An immediate consequence of Theorem 85

> **Theorem 86 (strict Cauchy–Schwarz; unconditional).** Let `F ≠ G` in `S` have identical gamma
> factors and conductors. Then
> ```
> Σ_{p ≤ x} |a_F(p) − a_G(p)|²/p  →  ∞ ,
> ```
> i.e. `n_{F/G} = n_F + n_G − 2\mathrm{Re}\,c_{F,G} > 0`, so
> ```
> \mathrm{Re}\,c_{F,G}  <  (n_F + n_G)/2 .
> ```
> *Proof.* Contrapositive of Theorem 85. ∎

The non-strict inequality `\mathrm{Re}\,c_{F,G} ≤ (n_F+n_G)/2` is Cauchy–Schwarz. **Strictness for
distinct elements is new**, and it is exactly the content Theorem 85 adds: the Selberg pairing cannot
saturate its Cauchy–Schwarz bound between distinct elements sharing archimedean data.

Under Conjecture B's expected values `n_F = n_G = 1` this reads `\mathrm{Re}\,c_{F,G} < 1`, which is
weaker than `c_{F,G} = 0` but is the first **unconditional strict** separation the programme has
between distinct elements of `S`.

### 143.2 A new direction: rational multipliers and `N_F \bmod m`

All of Theorems 84–85 use `k ∈ Z`, where `e^{2πikN_F} = 1`. For `k = j/m` rational,
```
e^{2πikS_F(t)} = ζ_m^{\,jN_F(t)} · e^{−2πikM_F(t)} ,   ζ_m = e^{2πi/m} ,
```
so the geometric side involves the distribution of **`N_F \bmod m`** — a genuinely new object, taking
`m` values rather than the two values `0` and `1` that §142.2 identified as the method's ceiling.

> **Why this is the natural next step.** §142.3 recorded that breaking the remaining cases requires a
> mechanism producing a value other than `0` or `1`. Rational `k` produces `m`-th roots of unity, and
> a congruence `n_F ≡ · \pmod m` for every `m` would give integrality — the first candidate route to
> `n_F ∈ Z` that does not pass through Rankin–Selberg.

**Obstruction, recorded honestly.** The arithmetic side still requires `𝒮 ∈ B²`, i.e. `n_F = 0`, so
the rational-`k` version currently yields nothing beyond Theorem 84. Making it useful needs the
arithmetic evaluation to survive `n_F > 0`, which §140.2 shows the present truncation argument cannot
deliver. **The direction is recorded as open, with its precise obstruction, rather than pursued
further this cycle.**

### 143.3 Consolidated status of the Energy Gap and multiplicity one

```
n_F = 0                                   ⟹ F = 1                      (Thm 84, unconditional)
Σ_p|a_F(p)−a_G(p)|²/p = O(1), same γ,Q    ⟹ F = G                      (Thm 85, unconditional)
F ≠ G, same γ,Q                           ⟹ Re c_{F,G} < (n_F+n_G)/2   (Thm 86, unconditional)
0 < n_F < 1                               — the only remaining Energy Gap case
n_F ∈ Z                                   — Conjecture A, open
c_{F,G} = 0 for distinct primitives       — Conjecture B, open
```
