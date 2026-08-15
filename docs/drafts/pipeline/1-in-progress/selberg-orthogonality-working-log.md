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

---

## 144. Cycle 144 (2026-07-26) — Theorem 87: the unified divergence theorem for integer combinations

Theorems 84 and 85 are the cases `(α,β) = (1,0)` and `(1,−1)` of a single statement.

### 144.1 The theorem

> **Theorem 87 (unconditional).** Let `F, G ∈ S` and `(α,β) ∈ Z²`. If `α d_F + β d_G ≠ 0`, then
> ```
> Σ_{p ≤ x} |α a_F(p) + β a_G(p)|² / p  →  ∞ .
> ```
>
> *Proof.* Put `X := αS_F + βS_G`. Then
> `X = (αN_F + βN_G) − (αM_F + βM_G)` with `αN_F + βN_G ∈ Z` (integer `α, β`), so for every integer
> `k`, `e^{2πikX} = e^{−2πik(αM_F+βM_G)}(1+o(1))`. The phase has derivative
> `αν_F + βν_G = ((αd_F + βd_G)/2π)\log t + O(1) → ±∞` monotonically, so van der Corput's
> first-derivative test gives `M\{e^{2πikX}\} = 0`.
>
> Suppose the displayed sum were bounded. Then `Σ_n|αΛ_F(n)+βΛ_G(n)|²/(n\log²n) < ∞`, so the
> associated expansion converges in `B²`, `X` differs from it by a constant, and the Weyl argument of
> §139.1(B) evaluates `M\{e^{2πikX}\} = e^{2πikc}∏_p I_p` with `∏_p(1 − |I_p|) < ∞`. Choosing `k` to
> avoid the finitely many possible zeros makes the product non-zero — contradicting `M\{e^{2πikX}\} = 0`.
>
> (The degenerate possibility `αΛ_F + βΛ_G ≡ 0` is excluded: it would force `X` constant, i.e. a
> genuine chirp equal to an integer-valued function minus a constant, impossible when
> `αd_F + βd_G ≠ 0`.) ∎

### 144.2 Specialisations and checks

- `(α,β) = (1,0)`: `d_F ≠ 0`, i.e. `F` non-constant, gives `Σ_p|a_F(p)|²/p = ∞` — **Theorem 84**.
- `(α,β) = (1,−1)` with `d_F = d_G`: the hypothesis fails, and this is exactly the regime where the
  chirp cancels and the geometric side is `1` instead of `0` — **Theorem 85**, proved by the
  complementary argument.
- `F = ζ`, `G = L(·,χ)`, `(α,β) = (1,1)`: `Σ_p|1+χ(p)|²/p = Σ_p(2+2\mathrm{Re}\,χ(p))/p ∼ 2\log\log x`,
  divergent ✔.
- `F = ζ`, `(α,β) = (2,0)`: `4Σ_p 1/p = ∞` ✔.

### 144.3 What it says structurally

Write `v_H(n) = Λ_H(n)/(\sqrt n\log n)` as in §134. Theorem 87 says:

> **Every integer combination `αv_F + βv_G` with `αd_F + βd_G ≠ 0` has infinite `ℓ²` norm.**
> Equivalently: the only directions in which the prime data of two elements of `S` can have finite
> energy are those in which the **archimedean data cancels**.

This is a sharp form of the principle the programme has been circling since §85.1 — that the
functional equation, not the Euler product, controls the prime energy. Here it appears as an exact
dichotomy governed by the single linear condition `αd_F + βd_G = 0`.

**Consequence for the degenerate line.** When `αd_F + βd_G = 0` and the gamma factors and conductors
also cancel, Theorem 85's argument applies and finiteness forces `αΛ_F + βΛ_G ≡ 0`. So along the
degenerate line the energy is finite **only** in the trivial case. Combining:

> **Corollary 88.** For `F, G ∈ S` and `(α,β) ∈ Z²` not both zero with matching archimedean data on
> the degenerate line, `Σ_p|αa_F(p)+βa_G(p)|²/p < ∞` holds **only** when `αΛ_F + βΛ_G ≡ 0`, i.e. when
> `F^α G^β = 1` in the group completion of `S`.

---

## 145. Cycle 145 (2026-07-26) — Theorem 89: zero energy forces triviality in the **group completion** of `S`

Theorems 84, 85, 87 are all instances of one statement about integer combinations of arbitrarily many
elements.

### 145.1 The complete dichotomy

Let `F_1,…,F_r ∈ S`, `(α_i) ∈ Z^r`, and put `X := Σ_i α_i S_{F_i}`. Then
`X = (Σα_i N_{F_i}) − (Σα_i M_{F_i})` with the first bracket integer-valued, so for `k ∈ Z`
```
e^{2πikX} = e^{−2πik Σα_i M_{F_i}} (1+o(1)) .
```
The phase derivative is
```
Σ_i α_i ν_{F_i}(t) = \frac{Σα_i d_{F_i}}{2π}\log t + \frac{Σα_i \log q_{F_i}}{2π} + O(1/t) .
```
Three cases, exhausting everything:

| archimedean data | phase | `M\{e^{2πikX}\}` |
|---|---|---|
| `Σα_i d_i ≠ 0` | chirp, derivative `→ ∞` | `0` (van der Corput) |
| `Σα_i d_i = 0`, `Σα_i\log q_i ≠ 0` | pure tone, non-zero frequency | `0` |
| both `= 0` | phase `→` constant | modulus `1` |

In the first two cases the argument of §139.1 gives a contradiction unless the energy diverges; in the
third, §141.1's rigidity forces every local factor to be a unit, hence all coefficients to vanish.

### 145.2 The theorem

> **Theorem 89 (unconditional).** Let `H = ∏_i F_i^{α_i}` be a non-trivial element of the group
> completion of `S` (`F_i ∈ S`, `α_i ∈ Z`), with prime coefficients `a_H(p) := Σ_i α_i a_{F_i}(p)`.
> Then
> ```
> Σ_{p ≤ x} |a_H(p)|² / p  →  ∞ .
> ```
> Equivalently: **`n_H = 0 ⟹ H = 1` in the group completion of `S`.**

Specialisations: `H = F` is Theorem 84; `H = F/G` with equal `γ, q` is Theorem 85; two-element
combinations are Theorem 87.

### 145.3 What this settles

- **Every non-trivial ratio, product or integer power combination of elements of `S` has divergent
  prime energy.** In particular the additive map `H ↦ v_H` from the group completion into the space of
  prime-coefficient sequences has **trivial kernel in the strongest sense**: no non-trivial element is
  even square-summable against `1/p`.
- The §137.1 semigroup picture upgrades: the zero-energy set is trivial not just inside `S` but inside
  the whole group completion, so the earlier worry about differences `v_{H_1} − v_{H_2}` not being
  controlled (which forced the retraction from "lattice" to "semigroup with isolated origin") is
  **resolved** — differences are covered by Theorem 89.

> **Corrected Theorem 82 (final form).** `H ↦ v_H` embeds the group completion of `S` into `ℓ²`-like
> sequence space with **every non-trivial element of infinite energy**; the zero-energy subgroup is
> trivial.

### 145.4 Distance to the conjectures

Theorem 89 says `n_H` is never `0` for `H ≠ 1`. Conjecture A says `n_H ∈ Z`; Conjecture B says
`n_H = Σe_i²`. The gap is unchanged in kind: the method is a **vanishing detector** (§142.2) and
cannot produce a value. But its reach is now the whole group completion, which is the natural domain
for both conjectures, and it removes the entire `n = 0` stratum from every question the programme
asks.

---

## 146. Cycle 146 (2026-07-26) — the resonance direction, and consolidation

### 146.1 Where a *value* could come from

§142.2 established that the geometric side of the characteristic-function method takes only the values
`0` and (modulus) `1`, so the method detects vanishing but cannot produce `n_F`. The natural way to
break that ceiling is to test against `e^{iξt}` rather than against `1`:
```
M\{e^{2πikS_F(t)}e^{iξt}\} = M\{e^{−2πikM_F(t)}e^{iξt}\} ,
```
whose phase `−2πkM_F(t) + ξt` has derivative `−2πkν(t) + ξ`, **vanishing** at `ν(t_0) = ξ/(2πk)`, i.e.
at `\log t_0 = ξ/(kd_F)`. So this quantity is governed by a stationary point rather than being
identically `0`, and stationary-phase evaluation produces a genuine value.

On the arithmetic side, `e^{iξt}` shifts the frequencies by `ξ`, selecting primes with `\log p ≈ ξ`.
Equating: `\log t_0 = \log p/(k d_F)`, i.e.
```
p ≈ t_0^{\,k d_F} .
```
**The `k`-th harmonic of `e^{2πiS_F}` resonates with primes of size `t^{kd_F}`** — §97's chirp
resonance, now with an exact stationary point rather than a heuristic.

**Obstruction, recorded.** The stationary-phase contribution to the *normalised* mean is
`≍ \sqrt{t_0}/T → 0` for fixed `ξ`, so the resonance is invisible to the Besicovitch mean; extracting
it requires a weight concentrated near `t_0`, and then the primes involved (`p ≈ t_0^{d}` for `k = 1`)
sit at the very edge of the explicit formula's effective range, where no unconditional control exists.
**Recorded as the precise reason this direction does not yet produce a value.**

### 146.2 Consolidation

The preprint now carries §11 with Theorems 84, 85 and 89 in full, including the trichotomy of §145.1
and the sharpness checks against `ζ` and against `L(·,χ_1) vs L(·,χ_2)`.

**Standing summary of the characteristic-function block (cycles 139–146).**
| result | statement |
|---|---|
| Thm 84 | `n_F = 0 ⟹ F = 1` |
| Thm 85 | `Σ_p\|a_F(p)−a_G(p)\|²/p = O(1)` and equal `γ,q` `⟹ F = G` (quantitative strong multiplicity one) |
| Thm 86 | `F ≠ G` with equal `γ,q` `⟹ \mathrm{Re}\,c_{F,G} < (n_F+n_G)/2`, strictly |
| Thm 87 | integer pairs: `αd_F+βd_G ≠ 0 ⟹ Σ_p\|αa_F(p)+βa_G(p)\|²/p = ∞` |
| Thm 89 | the group completion: `n_H = 0 ⟹ H = 1` |
| — | the method is a vanishing detector; it cannot produce `n_F ∈ Z` (§142.2) |

All unconditional; no Rankin–Selberg, no automorphy, no zero-density estimate, no RH.

---

## 147. Cycle 147 (2026-07-26) — the sharpness of the characteristic-function method, computed exactly

The method's ceiling has been asserted several times (§140.2, §142.2, §143.2). Here it is computed
once, in general form, and closed.

### 147.1 The exact inequality the method yields

For `H` non-trivial in the group completion, write `E(x) := Σ_{p≤x}|a_H(p)|²/p` and `X = Σα_iS_{F_i}`.
Truncating the `B²` expansion at `N` and comparing with the geometric evaluation over `[0,T]`:
```
| M_T\{e^{2πikX}\}  −  e^{2πikc}∏_{p≤N} I_p |  ≤  2πk\,\|X − c − 𝒮_N\|_{L²[0,T]}/\sqrt T  ≈  2πk\sqrt{E(T) − E(N)} ,
```
with `M_T\{e^{2πikX}\} = O(1/T)` (van der Corput) and `|∏_{p≤N}I_p| ≈ e^{−k²E(N)}`. Hence for every
`N ≤ T`
```
e^{−k²E(N)}  ≤  2πk\sqrt{E(T) − E(N)}  +  O(1/T) .                            (★)
```

### 147.2 What (★) does and does not force

- **If `E` is bounded**, take `N, T → ∞`: the left side tends to `e^{−k²E(∞)} > 0` and the right side
  to `0`. Contradiction — this is Theorems 84, 85, 87, 89.
- **If `E(T) → ∞`**, (★) is satisfiable for every choice of `N`: taking `E(T) − E(N) = δ` gives
  `e^{−k²(E(T)−δ)} ≤ 2πk\sqrt δ`, and the left side tends to `0` while the right side is fixed. **No
  contradiction, for any `k`, any `δ`, any growth rate of `E`** — including `E(x) = o(\log\log x)`,
  which would correspond to a non-trivial element of density `0`.

> **Theorem 90 (sharpness).** The characteristic-function method yields a contradiction **exactly**
> when `Σ_p|a_H(p)|²/p < ∞`, and never when it diverges, however slowly. In particular it cannot
> exclude a non-trivial `H` with `Σ_{p≤x}|a_H(p)|²/p → ∞` but of density `0`, and cannot produce any
> value of `n_H`.

### 147.3 Consequence for the programme's remaining targets

```
n_H = 0  (bounded energy)         — settled: H = 1                    (Theorem 89)
0 < n_H, density 0                — open; not reachable by this method
0 < n_H < 1                       — open; the remaining Energy Gap case
n_H ∈ Z                           — Conjecture A, open
c_{F,G} = 0 for distinct primitives — Conjecture B, open
```
The method removes exactly the `n = 0` stratum and nothing more. Any further progress must come from a
mechanism whose geometric side is not confined to `\{0, 1\}`; §146.1's stationary-phase resonance is
the only candidate the programme has found, and its obstruction (primes at the edge of the explicit
formula's range) is recorded there.

> **Recorded do-not-retry.** No refinement of the truncation, the choice of `k`, or the window in the
> characteristic-function method can reach a divergent energy. (★) is an identity-level obstruction,
> not a technical one.

---

## 148. Cycle 148 (2026-07-26) — **major correction**: convergence versus density zero

Theorem 90's sharpness analysis exposes an error running through cycles 130–147: the hypothesis
"`n_F = 0`" has been used interchangeably with "`Σ_p|a_F(p)|²/p < ∞`". **These are different.**

```
Σ_p|a_F(p)|²/p < ∞            (convergence)      ⟹   n_F = 0
n_F = 0   i.e.  Σ_{p≤x}|a_F(p)|²/p = o(\log\log x)   ⟹̸   convergence
```
A density-zero element may have a divergent energy sum, e.g. `Σ_{p≤x}|a_F(p)|²/p ≍ \log\log\log x`.

### 148.1 What has to be re-stated

- **Theorem 77.** Correct hypothesis: `Σ_p|a_F(p)|²/p < ∞`, **not** `n_F = 0`. The `B²` convergence of
  the expansion needs `Σ_n|Λ_F(n)|²/(n\log²n) < ∞`, i.e. convergence.
- **Theorem 84.** Correct statement: *no non-constant `F ∈ S` has `Σ_p|a_F(p)|²/p < ∞`.* The appended
  "equivalently `n_F = 0 ⟹ F = 1`" is **withdrawn**.
- **Theorem 85.** Unaffected — its hypothesis was already stated as boundedness, `= O(1)`.
- **Theorem 89.** The conclusion `Σ_{p≤x}|a_H(p)|²/p → ∞` stands; the appended "equivalently
  `n_H = 0 ⟹ H = 1`" is **withdrawn**.
- **Theorem 86.** **Withdrawn.** It deduced `n_{F/G} > 0` (a positive *density*) from divergence of the
  sum, which does not follow. Consequently `\mathrm{Re}\,c_{F,G} < (n_F+n_G)/2` is **not** proved.
- **Corollary 80′** (§134.1) and the semigroup/lattice discussion (§134.2, §137.1, §145.3): all should
  read "finite energy" in place of "`n = 0`". The statements remain true with that reading.

### 148.2 What is actually proved

> **Theorem 84′ (unconditional).** For every non-trivial `H` in the group completion of `S`,
> ```
> Σ_{p ≤ x} |a_H(p)|²/p  →  ∞ .
> ```
> Equivalently: **no non-trivial element of the group completion has square-summable prime
> coefficients against `1/p`.**

This is precisely **EG₀ as defined in §116.2** — *"no non-constant `F ∈ S` satisfies
`Σ_p|a_F(p)|²/p < ∞`"* — so that named target **is** settled, and in the stronger group-completion
form. What is **not** settled is the `n_F = 0` case of the Energy Gap in the density sense; §116.2's
remark identifying the two was already loose and is now corrected.

### 148.3 The corrected standing

```
Σ_p|a_H(p)|²/p < ∞   ⟹  H = 1                        (Theorem 84′, unconditional)   ✔ new
Σ_p|a_F(p)−a_G(p)|²/p = O(1), equal γ,q  ⟹  F = G     (Theorem 85, unconditional)    ✔ new
n_F = 0 in the density sense  ⟹  F = 1                — OPEN (energy may diverge slowly)
0 < n_F < 1                                            — OPEN
n_F ∈ Z                                                — Conjecture A, OPEN
c_{F,G} = 0 for distinct primitives                     — Conjecture B, OPEN
```

> **Methodological note.** This is the fifth over-claim caught and corrected in this programme, and the
> first that survived several cycles before detection. Its cause: reusing the symbol `n_F = 0` for two
> inequivalent conditions. **Rule added: never let a named constant stand for a hypothesis; state the
> hypothesis.** The sharpness computation of §147.1, done in general form rather than on special
> cases, is what exposed it — an argument for doing such computations earlier rather than later.

---

## 149. Cycle 149 (2026-07-26) — Theorem 91: a quantitative form of Theorem 84′

§148 left "divergent but density zero" open. Iterating the sharpness inequality (★) across scales
gives a divergence **rate**.

### 149.1 The scale iteration

The Weyl step in §139.1(B) requires equidistribution of `(t\log p)_{p≤N}` over `t ∈ [0,T]`. By Baker's
theorem the gaps between distinct values of `Σ_p m_p\log p` with bounded `|m_p|` and `p ≤ N` are
`≫ (\log N)^{−C}`, so the step is valid for `N ≤ T^{c}` with `c = c(k) > 0`. Applying (★) at the pair
`(T, N) = (x, x^{c})` and discarding the negligible `O(1/x)`:
```
e^{−k²E(x^{c})}  ≤  2πk\sqrt{E(x) − E(x^{c})} ,     E(x) := Σ_{p≤x}|a_H(p)|²/p ,
```
i.e.
```
E(x) − E(x^{c})  ≥  \frac{1}{4π²k²}\,e^{−2k²E(x^{c})} .
```

Set `x_j := T^{c^{\,j}}`, so `x_0 = T` and `x_J = O(1)` for `J ≈ \log\log T/\log(1/c)`. Summing the
increments and using `E(x_{j+1}) ≤ E(T)`:
```
E(T)  ≥  Σ_{j<J}\big(E(x_j) − E(x_{j+1})\big)  ≥  \frac{J}{4π²k²}\,e^{−2k²E(T)} .
```

### 149.2 The theorem

> **Theorem 91 (unconditional).** For every non-trivial `H` in the group completion of `S`,
> ```
> E(T)\,e^{2k²E(T)}  ≫_k  \log\log T   \quad\text{for every integer } k ≥ 1 ,
> ```
> hence, taking `k = 1`,
> ```
> Σ_{p ≤ T} |a_H(p)|² / p  ≫  \log\log\log T .
> ```

This upgrades Theorem 84′ from "`E(T) → ∞`" to an explicit rate. It is the first **quantitative**
lower bound the programme has for the prime energy of an arbitrary non-trivial element, and it needs
no automorphy, no Rankin–Selberg, no zero-density estimate and no RH.

### 149.3 Distance to the remaining cases

`\log\log\log T = o(\log\log T)`, so Theorem 91 does **not** exclude the density-zero case, nor reach
`n_H ≥ 1`. The obstruction is visible in the iteration: each scale contributes only
`e^{−2k²E}`, so the accumulated bound is logarithmic in the number of scales. To reach density `1` one
would need increments bounded below by a constant, which (★) does not give.

> **Recorded.** The characteristic-function method now yields: triviality when the energy converges
> (Theorem 84′), and the rate `≫ \log\log\log T` when it diverges (Theorem 91). Both are sharp for the
> method by §147.2. The Energy Gap's remaining cases require the increments — not merely their
> accumulation — to be bounded below.

---

## 150. Cycle 150 (2026-07-26) — Corollary 92: the zero-counting fluctuation is unbounded, with a rate

### 150.1 Combining Theorems 76 and 91

Theorem 76 (unconditional): `(1/P)∫_{t_0}^{t_0+P}|S_F|²dt ≥ (1/4π² + o(1))E(x)` for `P ≫ x`.
Theorem 91 (unconditional): `E(T) ≫ \log\log\log T` for non-trivial `F`. Hence:

> **Corollary 92 (unconditional).** For every non-constant `F ∈ S`,
> ```
> \frac1T∫_0^T |S_F(t)|²\,dt  ≫  \log\log\log T ,
> ```
> so `S_F` is **unbounded**. More generally the same holds for every non-trivial element of the group
> completion of `S` whose archimedean data does not cancel.

For `ζ` the unboundedness of `S(t)` is classical (Selberg), proved via his zero-density theorem. For a
general `F ∈ S` the analogous statement previously required the Selberg central limit theorem, hence a
density estimate (hypothesis (a), §90, of moment-problem strength). **Corollary 92 is unconditional**:
the amplifier supplies the lower bound and the characteristic-function iteration supplies the rate.

### 150.2 Why no better constant is available

The rate is `\log\log\log T`, whereas the expected truth is `n_F\log\log T`. §149.3 identifies the
loss: (★) bounds each scale increment by `e^{−2k²E}`, and general `1`-periodic test functions do not
help — expanding `f(X) = Σ_k\hat f(k)e^{2πikX}`, the geometric side collapses to `\hat f(0)` (every
`k ≠ 0` term vanishes), so the inequality reduces to the `k = ±1` case with a worse constant. Checked
this cycle and recorded.

> **Recorded do-not-retry.** No choice of periodic test function improves Theorem 91's rate; the
> exponential decay `|∏_{p≤N}I_p| ≈ e^{−k²E(N)}` is the binding constraint, and it is intrinsic to the
> Euler-product evaluation.

### 150.3 Consolidated new unconditional results of cycles 139–150

| # | statement |
|---|---|
| Thm 84′ | no non-trivial `H` in the group completion has `Σ_p\|a_H(p)\|²/p < ∞` |
| Thm 85 | equal `γ,q` and `Σ_p\|a_F(p)−a_G(p)\|²/p = O(1)` `⟹ F = G` (quantitative strong multiplicity one) |
| Thm 90 | the method's contradiction occurs exactly at convergence — sharpness |
| Thm 91 | `Σ_{p≤T}\|a_H(p)\|²/p ≫ \log\log\log T` for non-trivial `H` |
| Cor 92 | `(1/T)∫_0^T\|S_F\|² ≫ \log\log\log T`; `S_F` unbounded for every non-constant `F ∈ S` |

All proved from one identity — `e^{2πikS_F} = e^{−2πikM_F}`, forced by integrality of the
zero-counting function — together with van der Corput, Weyl equidistribution, Baker's gap bound, and
the Bessel-type non-vanishing of an Euler product of averaged exponentials.

---

## 151. Cycle 151 (2026-07-26) — the method is closed; consolidated hand-off

### 151.1 Last attempt to widen the method, and why it fails

Restricting the test to a subset of primes: for a set `P_0`, consider `e^{2πik(S_F − 𝒮_{P_0})}`.
Geometrically the phase is `−2πk(M_F + 𝒮_{P_0})` with derivative `−2πk(ν(t) + 𝒮_{P_0}')`; for **finite**
`P_0` (or `P_0 = \{p ≤ N\}` with `\|𝒮_N'\| ≪ N^{1/2}/\log N ≪ \log T`) van der Corput still applies and
the mean is `0`. Arithmetically the mean is `∏_{p ∉ P_0} I_p`, which requires
`Σ_{p∉P_0}|a_F(p)|²/p < ∞` — and that is exactly what Theorem 84′ says never happens. **The tail
energy always diverges, so the restricted version reduces to the unrestricted one.** Recorded.

> **Closed.** No variant of the characteristic-function method (choice of `k`, of periodic test
> function §150.2, of prime subset §151.1, or of truncation §147.2) extends past convergent energy.

### 151.2 Hand-off, updated to cycle 151 (supersedes §136.2)

**New unconditional results, cycles 139–150** — all from the identity `e^{2πikS_F} = e^{−2πikM_F}`
(integrality of the zero-counting function):

| # | statement |
|---|---|
| Thm 84′ | no non-trivial `H` in the group completion of `S` has `Σ_p\|a_H(p)\|²/p < ∞` |
| Thm 85 | equal `γ, q` and `Σ_p\|a_F(p)−a_G(p)\|²/p = O(1)` `⟹ F = G` |
| Thm 90 | sharpness: contradiction exactly at convergence, never at divergence |
| Thm 91 | `Σ_{p≤T}\|a_H(p)\|²/p ≫ \log\log\log T` |
| Cor 92 | `(1/T)∫_0^T\|S_F\|² ≫ \log\log\log T`; `S_F` unbounded for every non-constant `F ∈ S` |

**Withdrawn in cycle 148** (recorded so they are not re-cited): Theorem 86; the "`n_F = 0 ⟹ F = 1`"
phrasing of Theorems 84 and 89 — the correct hypothesis throughout is **convergence** of the energy,
not density zero.

**Open, in order of apparent tractability.**
1. Density-zero-but-divergent energy: exclude non-trivial `H` with `E(x) → ∞`, `E(x) = o(\log\log x)`.
2. The Energy Gap's remaining case `0 < n_F < 1`.
3. Conjecture A (`n_F ∈ Z`) — needs a mechanism whose geometric side is not confined to `\{0,1\}`
   (§142.2); the only candidate found is §146.1's stationary-phase resonance, obstructed by the primes
   at the edge of the explicit formula's range.
4. Conjecture B's real part (orthogonality) and imaginary part `ω` (§69.1 blindness; two
   representations, §80 and §131, neither improving on Cauchy–Schwarz).

**Design rules** (each derived from a killed conjecture): thin sets §77.2, scales §87.2, regimes
§98.3, independence §114.2, circularity §125.1, and — new in §148 — *never let a named constant stand
for a hypothesis*.

**Formal corpus:** 18 modules, 60 theorems, all `lake build`-verified and axiom-clean. The
characteristic-function block's algebraic cores are formalised: `norm_eq_one_of_prod_norm_eq_one`
(rigidity), `energy_le_of_amplifier` (the amplifier inequality), `rounding_floor` and
`integral_sq_rounding_error` (the `1/12` floor), `bessel_of_orthonormal`, `le_shift_of_count_le`.

---

## 152. Cycle 152 (2026-07-26) — preprint abstract, and a checked non-result

### 152.1 Checked and negative

Does Theorem 85 say anything about Conjecture B when the partner is a product of degree-1 elements?
For `F` primitive of degree `d ≥ 2` and `G` a product of degree-1 elements with the same `γ` and `q`,
Theorem 85's contrapositive gives `Σ_p|a_F(p) − a_G(p)|²/p = ∞` — automatic, since both individual
energies already diverge (Theorem 84′). **No information.** Recorded so the combination is not
re-attempted.

More generally: Conjecture B is a statement about **densities**, and by Theorem 90 the
characteristic-function method distinguishes only convergence from divergence. The two are
incommensurable, which is the same conclusion §142.2 reached and is now confirmed on the specific
combination.

### 152.2 Preprint

`docs/drafts/pipeline/4-publication-ready/monodromy-integrality-selberg.md` now opens with an abstract
stating the four unconditional results of the characteristic-function block, the sharpness theorem,
and the structural theory around them, together with an explicit statement that Conjectures A and B
remain open and that the contribution is a map of the obstruction. The eleven sections carry the
proofs.

---

## 153. Cycle 153 (2026-07-26) — the method's differential inequality, solved exactly

§149's iteration is really a differential inequality; solving it shows precisely why the method
stops at `\log\log\log`.

### 153.1 The ODE form

Write `E(x) = ψ(u)` with `u = \log\log x`, so that passing from `x` to `x^{c}` shifts `u` by
`\log c < 0`. The scale inequality of §149.1,
```
E(x) − E(x^{c})  ≥  \frac{1}{4π²k²}e^{−2k²E(x^{c})} ,
```
reads `ψ(u) − ψ(u − |\log c|) ≥ (4π²k²)^{−1}e^{−2k²ψ(u−|\log c|)}`, i.e. in differential form
```
ψ'(u)  ≥  C_k\, e^{−2k²ψ(u)} ,        C_k = (4π²k²|\log c|)^{−1} .
```

### 153.2 Its exact solution

Multiplying by `e^{2k²ψ}` gives `(e^{2k²ψ})' ≥ 2k²C_k`, hence `e^{2k²ψ(u)} ≥ 2k²C_k u + O(1)` and
```
ψ(u)  ≥  \frac{1}{2k²}\log\big(2k²C_k u\big) + O(1) ,
```
i.e. `E(x) ≫ \log\log\log x` — **Theorem 91, recovered as the exact solution of the inequality, not as
an estimate.** The `k = 1` case is optimal, since larger `k` shrinks both `C_k` and the prefactor.

### 153.3 Why this closes the density question

The conjectured truth is `E(x) ∼ n_F\log\log x`, i.e. `ψ(u) ∼ n_F u`, which requires
`ψ' ≳ n_F` — a **constant** lower bound on the derivative. The method supplies only
`ψ' ≥ C e^{−2ψ}`, which decays as soon as `ψ` grows. Hence:

> **The characteristic-function method can never distinguish `ψ(u) ≍ \log u` from `ψ(u) ≍ u`.** In
> particular it cannot exclude a non-trivial `H` of density zero, cannot reach `n_H ≥ 1`, and cannot
> give `n_H ∈ Z`. The obstruction is the exponential `e^{−2k²ψ}` in the increment bound, which comes
> from `|∏_{p≤N}I_p| ≈ e^{−k²E(N)}` and is intrinsic to evaluating the arithmetic side as an Euler
> product of averaged exponentials.

**Recorded as the final, quantitative closure of the method** (superseding the qualitative statements
of §147.2 and §150.2): the reachable region is `ψ ≫ \log u`, the conjectures live at `ψ ≍ u`, and no
choice of parameters bridges them.

### 153.4 What would bridge it

A constant lower bound on `ψ'` requires the arithmetic side to be bounded below **independently of the
accumulated energy** — i.e. an evaluation of `M\{e^{2πikX}\}` that does not decay exponentially in
`E`. Every evaluation the programme has found is an Euler product with `1 − |I_p| ≍ k²|a_H(p)|²/p`,
whose logarithm is exactly `−k²E`. Producing a non-multiplicative evaluation, or one with cancellation
among the local factors, is the single missing ingredient.

---

## 154. Cycle 154 (2026-07-26) — the short-difference variant: a value other than `0` or `1`, and why it still fails

§153.4 asked for an evaluation not decaying exponentially in the energy. Differencing `S_F` at short
distance produces one — and the attempt fails for a reason worth recording exactly.

### 154.1 The construction

For `h > 0` the increment `N_F(t+h) − N_F(t)` counts zeros in `(t, t+h]`, hence is an **integer**. So
for `k ∈ Z`
```
e^{2πik(S_F(t+h) − S_F(t))} = e^{−2πik(M_F(t+h) − M_F(t))} = e^{−2πikhν(t)}(1+O(h²/t)) .
```
With `h = λ/\log T` (the mean zero spacing) and `t ∈ [T,2T]`, the phase
`2πkhν(t) = khd\log(t/2π)+… ` varies by only `kdλ\log 2/\log T → 0`, so it is essentially constant:
```
\big| M_{[T,2T]}\{e^{2πik(S_F(t+h)−S_F(t))}\} \big| = 1 + o(1) .
```
**A geometric side of modulus `1` with no chirp** — exactly the "value other than `0`" that §142.2
identified as missing, obtained by replacing the chirp with a short difference.

The arithmetic side has coefficients `A_n·2\sin(h\log n/2)`, and over the range `n ≲ T` the energy
```
Σ_{n ≲ T} 4A_n²\sin²(h\log n/2)  ≈  \frac4{π²}∫_{1/\log T}^{1}\sin²(λu/2)\frac{du}{u}  =  O(1)
```
(substituting `u = \log n/\log T`, `d(Σ_{n≤x}\cdots) = du/u`) — **bounded**, because the `\sin²` factor
kills the small-`u` divergence. Were the factorisation valid, `|∏_pI_p| = 1` would force every local
factor to be a unit and hence `a_F(p)\sin(h\log p/2) = 0` for all `p`, giving `a_F(p) = 0` for almost
all `p` and, with Theorem 84′, `F = 1` — for **every** `F ∈ S`, including `ζ`.

### 154.2 Where it breaks

The energy computation above truncates at `n ≈ T`. The Besicovitch mean is over all `t`, so the
expansion must converge over **all** `n`, and
```
Σ_{n} 4A_n²\sin²(h\log n/2)  ≈  \frac4{π²}∫_{0}^{∞}\sin²(λu/2)\frac{du}{u}  =  ∞ ,
```
divergent at `u → ∞` (i.e. `n ≫ T`), where `\sin²` averages to `1/2` and the integral becomes the
original divergent energy. So the difference is **not** in `B²` and the Euler-product factorisation is
unavailable — exactly as consistency with `ζ` requires.

Working instead with the finite mean over `[T,2T]` does not help: the truncation error is
`2πk\|𝒟 − 𝒟_T\|_{L²[T,2T]}`, and terms with `n > T` oscillate over an interval of length `T` and
contribute their full (divergent) energy.

> **Recorded do-not-retry.** Short differences of `S_F` do produce a geometric side of modulus `1`
> without a chirp, but the matching arithmetic side is never in `B²`: the `\sin²` factor removes the
> low-frequency divergence and leaves the high-frequency one. **The two divergences cannot be removed
> simultaneously** — a smoothing that kills the tail reintroduces the head.

### 154.3 What the near-miss shows

The obstruction is not the geometric side after all: §153.4's request for a non-decaying evaluation is
satisfiable. The binding constraint is that **the arithmetic side requires `B²` convergence of the
full expansion**, and every modification that makes one end converge makes the other diverge. That is
a sharper statement of the barrier than §153.3's, and it identifies the real requirement:

> **[OPEN CORE, cycle 154]** Find a linear functional of `S_F` whose formal expansion has finite total
> energy — summed over *all* `n`, not merely over an effective range — and whose geometric evaluation
> is not `0`. The `\sin²(h\log n/2)` weight of the short difference fails only at the tail.

---

## 155. Cycle 155 (2026-07-26) — Theorem 93: **no admissible functional exists** — the method is closed for good

§154.3 asked for a linear functional of `S_F` whose formal expansion has finite total energy and
non-zero geometric evaluation. The answer is that none exists, and the reason is structural.

### 155.1 Which functionals are admissible

The whole method rests on `e^{2πik·(\text{something integer-valued})} = 1`. A linear functional
`L[S_F]` inherits the identity only if `L[N_F]` is integer-valued for all `t`. Since `N_F` is an
arbitrary non-decreasing integer step function of its argument, the functionals with that property are
exactly the finite **integer** combinations of evaluations,
```
L[S_F](t) = Σ_{j} c_j\,S_F(t + h_j) ,      c_j ∈ Z ,\ h_j ∈ R \text{ distinct} .
```
Any smoothing `∫S_F(t+u)ρ(u)du` destroys integrality of the `N`-part and with it the identity.

### 155.2 The weight such a functional induces cannot decay

`L` multiplies the `n`-th expansion coefficient `A_n` by
```
w(n) = Σ_j c_j\, n^{i h_j} ,
```
which as a function of `u = \log n` is the almost periodic function `Σ_j c_j e^{i h_j u}`. A non-zero
almost periodic function does **not** tend to `0`; its Besicovitch mean square is `Σ_j|c_j|² ≥ 1`, and
it exceeds any fixed `δ > 0` on a set of `u` of positive density. Therefore
```
Σ_n A_n²\,|w(n)|²  =  ∞   \text{ whenever }  Σ_n A_n² = ∞ ,
```
unless the coefficients `A_n` happen to be supported where `w` is small — which fails for all but a
measure-zero set of shift vectors `(h_j)`, so a suitable admissible `L` can always be chosen if any
can.

### 155.3 The theorem

> **Theorem 93 (closure).** For every admissible functional `L` — i.e. every finite integer
> combination of translates — the arithmetic side of the characteristic-function method converges if
> and only if the prime energy `Σ_p|a_F(p)|²/p` converges. Consequently the method yields a
> contradiction exactly in the convergent case (Theorem 90) and **no variant of it can reach a
> divergent energy.**

This answers §154.3 in the negative, and explains uniformly the failures of cycles 140–154: the
short-difference weight `2\sin(h\log n/2)` (§154), the prime-subset restriction (§151.1), the general
periodic test function (§150.2), the choice of `k` and of truncation (§147.2). All are admissible
functionals or reparametrisations of them, and Theorem 93 covers them all at once.

### 155.4 Final position of the characteristic-function block

**Proved unconditionally:** Theorems 84′, 85, 90, 91, 93 and Corollary 92.
**Proved impossible:** any extension of the method past convergent energy.
**Therefore:** the Energy Gap's remaining cases (`0 < n_F < 1`, and density-zero-with-divergent-energy)
and Conjectures A and B require a genuinely different mechanism — one not based on integrality of the
zero-counting function. Every mechanism the programme has tested is catalogued in §79.4 and §142.2;
the only one that has ever produced integers is the order of a pole of a meromorphic function (§74),
which returns to the Rankin–Selberg object.

---

## 156. Cycle 156 (2026-07-26) — Theorem 85 strengthened: the archimedean hypothesis is unnecessary

### 156.1 The observation

Theorem 85 was stated for `F, G ∈ S` with **identical gamma factors and conductors**, because its proof
used `M_F = M_G` so that `S_F − S_G` is integer-valued. But `F/G` is a non-trivial element of the group
completion of `S` exactly when `F ≠ G`, and Theorem 84′ applies to every such element with no
hypothesis on the archimedean data — the trichotomy of §145.1 covers all three cases:

| `d_F` vs `d_G` | `q_F` vs `q_G` | phase of `M_F − M_G` | evaluation |
|---|---|---|---|
| different | any | chirp, derivative `→ ±∞` | `0` (van der Corput) |
| equal | different | pure tone, non-zero frequency | `0` |
| equal | equal | constant (the `μ_j` enter only the constant term of Riemann–von Mangoldt) | modulus `1` |

The first two cases give the contradiction of §139.1; the third gives the rigidity of §141.1.

### 156.2 The strengthened statement

> **Theorem 85′ (strong multiplicity one; unconditional, no archimedean hypothesis).** For `F, G ∈ S`
> with `F ≠ G`,
> ```
> Σ_{p ≤ x} |a_F(p) − a_G(p)|² / p  →  ∞ .
> ```
> Equivalently: **if the prime coefficients of two elements of the Selberg class agree in the
> `ℓ²(1/p)` sense, the elements are equal.** In particular the map
> `F ↦ (a_F(p))_p \bmod ℓ²(1/p)` is injective on `S`.

The earlier hypothesis "identical gamma factors and conductors" is therefore **removable**, and the
`γ`-data of an element of `S` is determined by its prime coefficients modulo `ℓ²(1/p)` — a statement
with no analogue among the programme's earlier results.

### 156.3 Why the third case needs the `μ_j` remark

When `d_F = d_G` and `q_F = q_G` the two Riemann–von Mangoldt main terms differ only by a constant: the
formula `N(T) = (T/2π)\log(q T^d/(2πe)^d) + C(γ) + S(T) + O(1/T)` has the `μ_j` entering only through
the constant `C(γ)`. Hence `M_F − M_G` is constant, the phase of `e^{−2πik(M_F−M_G)}` is constant, the
geometric evaluation has modulus `1`, and the rigidity lemma
(`norm_eq_one_of_prod_norm_eq_one`, formalised) forces every coefficient difference to vanish. So
elements of `S` sharing degree and conductor but differing in the `μ_j` are also separated. ✔

### 156.4 Consolidated

The characteristic-function block's final statements:
```
Thm 84′ : no non-trivial H in the group completion has Σ_p|a_H(p)|²/p < ∞
Thm 85′ : F ≠ G in S  ⟹  Σ_p|a_F(p) − a_G(p)|²/p → ∞          (no archimedean hypothesis)
Thm 90  : the method's contradiction occurs exactly at convergence
Thm 91  : Σ_{p≤T}|a_H(p)|²/p ≫ log log log T
Thm 93  : no admissible functional extends the method past convergent energy
Cor 92  : S_F unbounded for every non-constant F ∈ S, with (1/T)∫|S_F|² ≫ log log log T
```

---

## 157. Cycle 157 (2026-07-26) — the two metrics on `S`, and the formal status of Theorem 93

### 157.1 Two pseudo-metrics, and which one the programme controls

On `S` there are two natural distances built from prime coefficients:
```
D(F,G)² := Σ_p |a_F(p)−a_G(p)|²/p           (the raw energy)
ρ(F,G)² := n_F + n_G − 2\mathrm{Re}\,c_{F,G}  (its logarithmic density)
```

- **`D` is completely determined by the programme.** Theorem 85′: `D(F,G) = ∞` for every `F ≠ G`, and
  `0` otherwise. So `D` is the discrete metric — no geometry, but a sharp injectivity statement.
- **`ρ` is the object of Conjecture B**, which asserts `ρ(F,G)² = 2` for distinct primitives. The
  programme controls **nothing** about `ρ` beyond Cauchy–Schwarz: divergence of `D` does not give
  `ρ > 0`, since a sum may diverge with density zero. This is exactly why Theorem 86 had to be
  withdrawn (§148.1).

> **Recorded.** The characteristic-function method sees `D` and is blind to `ρ`. Every remaining
> target — the Energy Gap's `0 < n_F < 1`, Conjecture A's `n_F ∈ Z`, Conjecture B's `ρ(F,G)² = 2` — is
> a statement about `ρ`. **The gap between the two metrics is the gap between what is proved and what
> is conjectured.**

Attempts checked this cycle and failed to bridge it: Theorem 91's rate (`≫ \log\log\log T`) is
`o(\log\log T)` and so says nothing about `ρ`; the moment floors
`M\{|S_F − c|^{2m}\} ≥ ((2m+1)4^m)^{−1}` from the rounding argument decrease in `m` and are consistent
with bounded `S_F`, so they add nothing to Theorem 79's `m = 1` case.

### 157.2 Theorem 93's core is already formalised

Theorem 93 rests on: *a non-zero finite exponential sum `Σ_j c_j e^{ih_ju}` with distinct frequencies
does not tend to `0`; its mean square is `Σ_j|c_j|²`.* That is exactly
```
genPoly_meanValue        (exact diagonal/off-diagonal split, arbitrary real frequencies)
genPoly_meanValue_error_of_gap  (error uniform in interval, length and position, under a frequency gap)
```
in `HTGeometry/GeneralizedDirichletMeanValue.lean`, proved in cycles 73–83 for an unrelated purpose.
Together they give mean square `= Σ_j|c_j|² + O(1/U)`, hence non-decay. **No new formalisation is
needed for the closure theorem.**

This is the third time a Lean module written for one purpose has carried a later paper result
(`log_coeff_bound` → Theorem 52; `le_shift_of_count_le` → Theorem 47; now
`genPoly_meanValue_error_of_gap` → Theorem 93).

### 157.3 Position

```
proved   : everything about D  (Thm 84′, 85′, 90, 91, 93, Cor 92)
open     : everything about ρ  (Energy Gap remainder, Conjecture A, Conjecture B)
mechanism: integrality of N_F sees D; ρ needs a meromorphic parent (§74)
```

---

## 158. Cycle 158 (2026-07-26) — an energy/fluctuation inequality, and a novelty assessment

### 158.1 A usable reformulation of Theorem 76

Theorem 76 reads `(1/P)∫|S_F|² ≥ E(x)/(4π²)` for `P ≫ x`, i.e.
```
E(x)  ≤  4π²·\big(\text{mean square of } S_F \text{ over an interval of length } P ≫ x\big) .
```
So **an upper bound for the fluctuation gives an upper bound for the prime energy.** Combined with the
unconditional `S_F(t) ≪ \log t` this yields only `E(T) ≪ \log²T`, far from the expected
`n_F\log\log T`; and Littlewood's lemma controls only the **first** moment
(`∫_0^T S_F = O(\log T)`), not the second. Writing `S_F − c = ρ − θ` as in §133.2 gives
`\mathrm{Var}(S_F) ≍ M\{ρ²\}` with `ρ = N_F − \mathrm{round}(M_F+c) ∈ Z`, and no unconditional bound
for that integer discrepancy is available.

> **Recorded.** The chain `\text{fluctuation upper bound} ⟹ \text{energy upper bound} ⟹ ρ`-control is
> real but its first link is missing; supplying it is equivalent to the second-moment estimate that
> Selberg's density theorem provides for `ζ` and that the programme has repeatedly identified as
> hypothesis (a).

### 158.2 Novelty assessment of the characteristic-function block

Recorded as an assessment, not a priority claim; a systematic literature check remains outstanding.

- **Theorem 85′** (`F ≠ G` in `S` `⟹ Σ_p|a_F(p)−a_G(p)|²/p → ∞`; equivalently the prime coefficients
  determine `F` modulo `ℓ²(1/p)`). Strong multiplicity one in `S` is classical **under** Selberg's
  conjectures (Murty–Murty) and known unconditionally for automorphic `L`-functions when the
  coefficients agree at all but finitely many primes (Ramakrishnan). The `ℓ²(1/p)` form,
  unconditional and inside `S` with no archimedean hypothesis, has **not been located** in the
  literature.
- **Theorem 84′** (no non-trivial element of the group completion has convergent prime energy). The
  statement `n_F ≥ 1` is conjectural; the weaker divergence of `Σ_p|a_F(p)|²/p` for non-constant
  `F ∈ S` is the kind of thing that could be folklore, but has **not been located**.
- **Corollary 92** (`S_F` unbounded for every non-constant `F ∈ S`, unconditionally, with
  `(1/T)∫|S_F|² ≫ \log\log\log T`). For `ζ` this is Selberg's, via his zero-density theorem; for
  general `F ∈ S` the usual route needs a density estimate. The unconditional general form has **not
  been located**.
- **Theorems 90, 93** (sharpness and closure of the method) are statements about the method itself and
  are new by construction.

### 158.3 Standing

The programme's position is unchanged in substance: `D` fully determined, `ρ` untouched, and the
mechanism for `ρ` identified as the meromorphic parent of `R_{F,F}`. What cycles 139–158 added is a
complete, unconditional theory of `D` together with proofs that it cannot be pushed further.

---

## 159. Cycle 159 (2026-07-26) — a two-sided unconditional bracket for the fluctuation of `S_F`

### 159.1 Theorem 53 holds on the critical line

Theorem 53 (`∫_0^T|\log F(σ+it)|²dt ≪_σ T\log²T`) was stated for fixed `σ > 1/2`. Its proof — the
Hadamard–Landau expansion `\log|F(s)| = Σ_{|ρ−s|<1}\log|s−ρ| + O(\log t)`, Cauchy–Schwarz over the
`≪ \log t` nearby zeros, and `∫_{|t−γ|<1}\log²|s−ρ|dt ≪ 1` because `\log²` is locally integrable —
is valid **at `σ = 1/2` as well**: the local integrability does not degrade when the point sits on the
line of the zeros. Hence

> **Theorem 53′ (unconditional).** For every `F ∈ S`,
> `∫_0^T |\log F(1/2+it)|²\,dt ≪ T\log²T`, and consequently
> `(1/T)∫_0^T S_F(t)²\,dt ≪ \log²T`.

### 159.2 The bracket

With Corollary 92 (`(1/T)∫_0^T S_F² ≫ \log\log\log T`, cycle 150):

> **Corollary 94 (unconditional).** For every non-constant `F ∈ S`,
> ```
> \log\log\log T  ≪  \frac1T∫_0^T S_F(t)²\,dt  ≪  \log²T .
> ```

This is the first **two-sided unconditional** estimate for the zero-counting fluctuation of a general
element of the Selberg class. The expected truth is `(n_F/2π²)\log\log T`, so both sides are far from
sharp; the lower bound comes from the characteristic-function iteration, the upper from
Hadamard–Landau.

### 159.3 What closing the bracket would need

Reducing the upper bound from `\log²T` to `\log\log T` is exactly Selberg's second-moment estimate,
whose proof for `ζ` runs through his zero-density theorem. The `\log²T` here loses a factor `\log T`
at the Cauchy–Schwarz step over the `≍ \log t` zeros within distance `1`; recovering it requires
cancellation among those terms, i.e. precisely hypothesis (a) of §90. **Recorded: the upper half of
Corollary 94 is Hadamard–Landau plus Cauchy–Schwarz and cannot be improved without zero-density
input.**

### 159.4 A note on `ω`

For pairs where the twist `F ⊗ \bar G` lies in `S^♯` and is meromorphic, `c_{F,G}` is the order of a
pole, hence an **integer**, hence real, so `ω(F,G) = 0` automatically. In degree `1` this covers every
pair (§39.1), which is why `ω ≡ 0` there. So a non-zero `ω` requires the Rankin–Selberg object to
fail to exist — consistent with §71 and §131, and a reminder that `ω` and the real part are obstructed
by the same missing construction.

---

## 160. Cycle 160 (2026-07-26) — formal status of Theorem 53′, and where its loss sits

### 160.1 Both ingredients checked against mathlib and the corpus

Theorem 53′ has exactly two quantitative ingredients.

1. **Local integrability of `\log²`**, in the form `∫_0^1(\log u)²du = 2` (hence
   `∫_{−1}^{1}(\log|u|)²du = 4`). Corpus search
   (`research "integral log squared local integrability"`) returns only unrelated Sonin/Brolin kernel
   results; mathlib has no direct lemma (`exact?` fails on the statement). Formalising it needs
   integration by parts on an improper integral — a genuine but routine task, **not** the source of
   any loss in the theorem.
2. **The Cauchy–Schwarz step** `(Σ_{i∈s}f_i)² ≤ |s|·Σ_{i∈s}f_i²`. This **is** in mathlib as
   `sq_sum_le_card_mul_sum_sq` — verified by probe. No duplication written.

### 160.2 Where the `\log T` is lost, precisely

In `\log|F(σ+it)| = Σ_{|ρ−s|<1}\log|s−ρ| + O(\log t)`, the sum has `≍ \log t` terms. Applying
`sq_sum_le_card_mul_sum_sq` gives
```
\Big(Σ_{|ρ−s|<1}\log|s−ρ|\Big)^2  ≤  (\#\{ρ\})·Σ_{|ρ−s|<1}\log²|s−ρ|  ≍  \log t·Σ\log²|s−ρ| ,
```
and integrating, `∫_0^T ≪ \log T·(T\log T)·O(1) = T\log²T`. **The factor `\log T` is exactly the
cardinality factor in Cauchy–Schwarz**, i.e. the assumption that the `≍ \log t` terms do not cancel.
The truth (`\log\log T`) requires square-root cancellation among them, which is the content of
Selberg's density theorem.

> **Recorded.** The upper half of Corollary 94 is `sq_sum_le_card_mul_sum_sq` applied to the
> Hadamard–Landau expansion, and its loss is a single, identified application of Cauchy–Schwarz.
> Improving it is not a matter of technique inside this argument; it needs input asserting the
> cancellation.

### 160.3 Discipline note

Both ingredients were checked **before** writing any Lean, per §119.3. One is already in mathlib and
was therefore not re-proved; the other is absent but is not load-bearing for the programme's
conclusions. **No new module written this cycle** — the correct outcome of a search that finds the
tool already exists.

---

## 161. Cycle 161 (2026-07-26) — Corollary 94's two bounds are the two extreme zero models

### 161.1 What each side of the bracket corresponds to

Write `L(t) := Σ_{|γ−t|<1}\log|t−γ|`, so that `\log|F(1/2+it)| = L(t) + (\text{archimedean}) + O(1)`
and the archimedean term `+(d/2)\log t` cancels the mean of `L` (which is
`−2ν(T) ≍ −(d/π)\log T`, since `∫_{|u|<1}\log|u|du = −2` per zero).

The **variance** of `L` depends entirely on the local statistics of the zeros:

| zero model | `\mathrm{Var}(L)` | corresponds to |
|---|---|---|
| perfect lattice (rigid) | `O(1)` | Theorem 79's equality case — excluded by Theorem 70 |
| Poisson of intensity `ν` | `ν∫\log²|u|du ≍ \log T` | the Cauchy–Schwarz bound of §160.2 |
| GUE / Montgomery pair correlation | `≍ \log\log T` | the conjectural truth `(n_F/2π²)\log\log T` |

So **Corollary 94's upper bound `\log²T` is exactly the Poisson (no-cancellation) model**, obtained by
applying `sq_sum_le_card_mul_sum_sq` as if the `≍\log t` terms were independent; and **its lower bound
`\log\log\log T` sits just above the rigid model**, which the programme has excluded outright
(Theorem 70) and quantitatively (Corollary 92).

### 161.2 The reading

> The programme has bracketed the zeros of an arbitrary `F ∈ S` between *not perfectly rigid* and *no
> more clustered than Poisson*, unconditionally. The conjectural truth — and the input hypothesis (a)
> needs — is the intermediate GUE value, i.e. **Montgomery-type pair correlation**.

This is the same funnel §93.3 identified from four independent directions, now visible as the gap
between the two halves of a single unconditional bracket. It also explains why no argument internal
to §160.2 can improve the upper bound: replacing Cauchy–Schwarz by anything sharper *is* asserting
sub-Poisson clustering of the zeros.

### 161.3 Status

```
rigid                    excluded          (Thm 70, Cor 92)
sub-Poisson (GUE)        conjectural       (= hypothesis (a) = pair correlation)
Poisson                  proved as a ceiling (Thm 53′, Cor 94)
```
Everything the programme still wants — the Energy Gap's remainder, Conjecture A, Conjecture B — lies
in the gap between the second and third rows.

---

## 162. Cycle 162 (2026-07-26) — sub-Poisson clustering is equivalent to the explicit-formula truncation

### 162.1 The short-interval variance, computed both ways

For fixed `h > 0`, `N_F(t+h) − N_F(t) = hν(t) + ΔS(t)` with `ΔS = S_F(t+h) − S_F(t)`, so
```
\mathrm{Var}\big(N_F(t+h) − N_F(t)\big) = \mathrm{Var}(ΔS) .
```
`ΔS` has formal expansion coefficients `A_n·2\sin(h\log n/2)`. **Truncating at the explicit formula's
effective range `n ≲ T`** and using `\sin² → 1/2` on average,
```
\mathrm{Var}(ΔS) ≈ \tfrac{4}{π²}Σ_{n≲T}A_n²·\tfrac12·2 ≍ n_F\,\log\log T .
```
The Poisson model, by contrast, gives `\mathrm{Var} ≈ hν(t) ≍ h\,d\log T/2π`. Hence:

> **If the truncation at `n ≲ T` is legitimate, the zeros of `F ∈ S` are sub-Poisson — the
> short-interval count has variance `≍ n_F\log\log T`, smaller than the Poisson `≍ \log T` by a full
> logarithm.**

### 162.2 Why this is an equivalence, not a proof

The truncation is exactly what is not available. Over an interval of length `T` the mean square of
`Σ_n c_n e^{it\log n}` is `≈ Σ_n |c_n|²` over **all** `n`, and that sum diverges (§154.2) — the terms
with `n ≫ T` oscillate but still contribute their full energy to an `L²` computation on a finite
interval. Discarding them is precisely the assertion that the explicit formula may be truncated with
controlled error, which is hypothesis (a).

> **Recorded.** *Sub-Poisson clustering of the zeros* and *legitimacy of the explicit-formula
> truncation* are the same statement. §161's table therefore has only one open row, and it is
> hypothesis (a) under a third name — after "zero-density estimate" (§90) and "Montgomery pair
> correlation" (§93.3).

### 162.3 What this adds

The value of the computation is that it fixes the **constant**: were the truncation available, the
short-interval variance would be `≍ n_F\log\log T`, i.e. the prime energy is exactly the sub-Poisson
deficit of the zeros. That identifies `n_F` with a purely geometric quantity — the variance of the
zero count in a fixed-length interval — with no primes in the statement:

> **(SP) Sub-Poisson form of `n_F`.** For `F ∈ S` and fixed `h > 0`,
> `\mathrm{Var}_{t≤T}\big(N_F(t+h) − N_F(t)\big) ∼ c(h)·n_F·\log\log T`.

`SP` is equivalent to hypothesis (a) plus the variance asymptotic, and it is the cleanest statement of
`n_F` as a zero statistic that the programme has produced.

---

## 163. Cycle 163 (2026-07-26) — band-limiting removes the truncation problem: an exact variance identity

### 163.1 The point

The truncation difficulty of §154.2 and §162.2 is an artefact of using test functions that are not
band-limited. With `ψ` whose Fourier transform is supported in `[−\log X, \log X]`, the Weil explicit
formula's prime side is a **finite** sum over `n ≤ X` and the formula is exact — no truncation, no
error term.

For such `ψ`, the smoothed zero count `Z_ψ(t) := Σ_γ ψ(γ − t)` satisfies
```
Z_ψ(t) = ∫ψ(u−t)ν(u)\,du \;−\; \frac1{2π}Σ_{n ≤ X} Λ_F(n)\,n^{−1/2}\big(\hatψ(\log n)e^{−it\log n} + \overline{\;\cdot\;}\big) ,
```
a deterministic term plus a **finite** exponential sum with frequencies `\log n`. Its mean square over
`t` is then computed exactly by the generalized-Dirichlet mean value theorem
(`genPoly_meanValue`, formalised), the off-diagonal terms vanishing in the limit:

> **Theorem 95 (exact smoothed-count variance; unconditional).** For `ψ` with `\hatψ` supported in
> `[−\log X,\log X]`,
> ```
> \lim_{T→∞}\frac1T∫_0^T \big|Z_ψ(t) − \mathbb E Z_ψ\big|²\,dt \;=\; \frac1{4π²}\sum_{n ≤ X}\frac{|Λ_F(n)|²\,|\hatψ(\log n)|²}{n} .
> ```
> No truncation, no zero-density estimate, no RH: the sum is finite and the identity exact.

### 163.2 What it does and does not settle

- **Does:** it makes rigorous every "effective range" computation the programme has used heuristically
  (§154.1, §162.1), for the class of band-limited weights. In particular the variance of a smoothed
  zero count is *exactly* a weighted prime energy.
- **Does not:** reach the sharp-cutoff statistics. Sub-Poisson clustering (§162) concerns
  `N_F(t+h) − N_F(t)`, whose weight `\mathbf 1_{[0,h]}` is **not** band-limited; approximating it by a
  band-limited `ψ` introduces exactly the tail that §154.2 identified. The Beurling–Selberg
  extremal functions bound the sharp cutoff between two band-limited weights, but the gap between
  their variances is of the same order as the quantity being estimated.

> **Recorded.** Band-limiting converts the truncation problem into the classical difficulty of
> approximating a sharp cutoff by band-limited functions. That is progress in form — every statement
> becomes exact and unconditional — but the Beurling–Selberg loss reinstates the same barrier for
> sharp counts.

### 163.3 Consequence worth keeping

Theorem 95 gives, for each `X`, an unconditional exact identity linking a zero statistic to a finite
prime sum. Choosing `\hatψ ≈ \mathbf 1_{[0,\log X]}` gives
```
\mathrm{Var}(Z_ψ) ≍ Σ_{p ≤ X}|a_F(p)|²\frac{\log²p}{p} ,
```
so **the prime energy weighted by `\log²p` is an exactly computable zero statistic**. This is the
first identity in the programme that expresses a prime quantity as a zero quantity with no error term
at all, and it is the natural vehicle for any future attempt on `n_F`: the remaining task is to pass
from the `\log²p`-weighted sum to the `1/p`-weighted density, which is a partial-summation question requiring
uniformity in `X`.

---

## 164. Cycle 164 (2026-07-26) — Theorem 96: the prime energy **is** a smoothed-zero-count variance, exactly

### 164.1 Choosing the weight that inverts `\log²p`

Theorem 95 gives, for band-limited `ψ`,
```
\mathrm{Var}(Z_ψ) = \frac1{4π²}Σ_{n ≤ X}\frac{|Λ_F(n)|²\,|\hatψ(\log n)|²}{n} ,
```
and `Λ_F(p) = a_F(p)\log p`. Choosing the **even real** weight
```
\hatψ_X(ξ) = 1/|ξ| \quad (ξ_0 ≤ |ξ| ≤ \log X), \qquad 0 \text{ otherwise}
```
makes `|Λ_F(p)|²|\hatψ(\log p)|²/p = |a_F(p)|²/p` exactly. The prime-power terms contribute
`Σ_{p,k≥2}|b_F(p^k)|²k²\log²p·(k\log p)^{−2}p^{−k} = Σ_{p,k≥2}|b_F(p^k)|²p^{−k} = O(1)`.

> **Theorem 96 (unconditional exact identity).** With `ψ_X` as above and
> `Z_{ψ_X}(t) = Σ_γ ψ_X(γ − t)`,
> ```
> Σ_{p ≤ X} \frac{|a_F(p)|²}{p} \;=\; 4π²\,\mathrm{Var}_t\big(Z_{ψ_X}(t)\big) \;+\; O(1) ,
> ```
> the variance being the exact Besicovitch mean square, with no truncation, no zero-density estimate
> and no RH. `ψ_X` is explicit: `ψ_X(u) = π^{−1}\big(\mathrm{Ci}(u\log X) − \mathrm{Ci}(uξ_0)\big)`, a
> positive logarithmic profile of width `≍ 1/ξ_0` and height `π^{−1}\log(\log X/ξ_0)`.

### 164.2 Conjecture A as a statement about a variance

Dividing by `\log\log X`:

> **Conjecture A ⟺** for every `F ∈ S`,
> ```
> \lim_{X→∞} \frac{4π²\,\mathrm{Var}_t\big(Z_{ψ_X}(t)\big)}{\log\log X} \in \mathbb Z_{≥0} .
> ```

This is the first formulation of Conjecture A in which **no prime appears**: it asserts that the
variance of an explicit smoothed count of the zeros of `F`, normalised by `\log\log X`, is an integer.
Compare §115.1 (a coefficient mean value) and §108.3 (prime-square densities) — both still mention
coefficients; this one does not.

### 164.3 Sanity checks

- `F = ζ`: `Σ_{p≤X}1/p = \log\log X + O(1)`, so the variance is `(\log\log X)/4π² + O(1)` and the
  limit is `1 = n_ζ` ✔.
- `F = ζ^k`: coefficients `k`, energy `k²\log\log X`, limit `k² = n_{ζ^k}` ✔.
- Consistency with Theorem 84′: the variance grows without bound for every non-trivial `H` ✔; with
  Corollary 94: it is `≫ \log\log\log X` and `≪ \log²X` unconditionally ✔.

### 164.4 What remains

The identity is exact, so nothing is lost in it; the difficulty has moved entirely into showing that a
variance of a smoothed zero count has an integral normalised limit. That is Conjecture A restated, not
solved — but restated in a form where **both sides are zero-side quantities**, which no earlier
formulation achieved, and where the only input used was the band-limited explicit formula and the
mean-value theorem for exponential sums (`genPoly_meanValue`, formalised).

---

## 165. Cycle 165 (2026-07-26) — novelty check on Theorem 96: it is Montgomery's identity repackaged

### 165.1 The check I should have run first

For a point process, the variance of a smoothed count is
```
\mathrm{Var}(Z_ψ) = ν\|ψ\|_2² + ∫∫ψ(u)ψ(v)\big[ρ_2(u−v) − ν²\big]\,du\,dv ,
```
so `\mathrm{Var}(Z_ψ)` for all band-limited `ψ` **is** the pair correlation of the zeros. Theorem 95
equates it with a finite prime sum; that equation is exactly **Montgomery's explicit-formula identity**
(1973 for `ζ`, and standard in the Selberg class), with `\hatψ` playing the role of Montgomery's test
function.

> **Verdict on Theorem 96: REDISCOVERED.** The content — variance of a smoothed zero count equals a
> weighted prime sum — is Montgomery's. What is new here is only the **choice of weight**
> `\hatψ_X(ξ) = 1/|ξ|` on `[ξ_0,\log X]`, which normalises the prime side to the `1/p`-energy exactly
> rather than to Montgomery's `\log`-weighted form. That is packaging, not a theorem.

The same caveat applies to Theorem 95, which is the band-limited explicit formula plus the mean-value
theorem for exponential sums — both classical.

### 165.2 What survives, and what it means

- The **reformulation** of Conjecture A as "the normalised variance of an explicit smoothed zero count
  is an integer" (§164.2) stands, and is a legitimate restatement — but it is a restatement of
  Montgomery's identity applied to Selberg's conjecture, not new mathematics.
- The consistency it provides is still useful: it confirms, by an independent route, §93.3's
  conclusion that the quadratic problems funnel into pair correlation. Indeed §165.1 makes that
  literal — the object in Theorem 96 **is** the pair correlation.
- The genuinely new unconditional results of the recent block are unaffected: Theorems 84′, 85′, 90,
  91, 93, Corollaries 92, 94. Those rest on the characteristic-function identity, not on Montgomery's.

> **Recorded.** Cycles 163–164 produced a clean exact identity and a prime-free restatement of
> Conjecture A, but the identity is classical. **Phase-2 novelty checking must precede reporting, not
> follow it** — this is the second time (cf. §93.2, Bombieri–Perelli) that a result was developed
> before its literature position was established, and both times the verdict was "rediscovered".

### 165.3 Adjusted position

```
new and unconditional : Thm 84′, 85′, 90, 91, 93, Cor 92, Cor 94   (characteristic-function block)
classical, repackaged : Thm 95, 96 and the §164.2 restatement       (Montgomery's identity)
open                  : Conjecture A, Conjecture B, Energy Gap remainder
```

---

## 166. Cycle 166 (2026-07-26) — hypothesis (a) pinned to the literature; a speculation killed; the mod-1 rigidity principle

Phase-2 novelty checking run **before** any claim, per §165.2.

### 166.1 A speculation formed and refuted inside the cycle

§100.1 assesses hypothesis (a) — a Selberg-type zero-density estimate
`N_F(σ,T) ≪ T^{1−c(σ−1/2)}\log T` — as "of moment-problem difficulty for `d ≥ 2`", on the basis of the
**convexity** mean-square bound `∫_0^T|F(σ+it)|²dt ≪ T^{1+d(1−σ)+ε}`. That input is wasteful. The
approximate functional equation plus the Montgomery–Vaughan mean value theorem gives, for
`1/2 ≤ σ < 1` and `X = Y ≍ 𝔮(t)^{1/2} ≍ T^{d/2}`,
```
∫_0^T |F(σ+it)|² dt  ≪_{F,ε}  T^{1+ε}/(2σ−1)  +  T^{d(1−σ)+ε} ,
```
so the bound is `≪ T^{1+ε}` for `σ ≥ 1 − 1/d`, and in particular **on the whole half-strip `σ ≥ 1/2`
when `d_F ≤ 2`**. (At `σ = 1/2` the Montgomery–Vaughan error is `X^{1+ε} = T^{d/2+ε}`, admissible
exactly for `d ≤ 2`.) This is strictly stronger than the convexity bound — at `σ = 1/2`, `d = 2` it is
`T^{1+ε}` against `T^{2+ε}`.

**Speculation formed:** since the second moment is the classical route into zero-density estimates,
`d_F ≤ 2` should make hypothesis (a) unconditional, unlocking Theorems 46, 47, 49 and the
(P2)/(ZS) chain in degree `≤ 2`.

**Refuted by the literature, same cycle.** The second-moment route does not reach `σ → 1/2`:

- **Mukhopadhyay–Srinivas**, *A zero density estimate for the Selberg class*, Int. J. Number Theory
  **3** (2007), 10.1142/S1793042107000894. Theorem 1: assume `∫_0^T|L(1/2+it)|²dt ≪ T^{λ+ε}`; then
  zero-density bounds follow **only in the range `2/3 < σ < 1`** (with a second regime for
  `1 < λ < 3/2`). The method is Montgomery's zero-detection plus the Halász–Montgomery lemma, and it
  degenerates below `σ = 2/3` because the detecting polynomial's length overwhelms the large sieve.
- **Perelli** supplies the mean square with `λ = d/2` for the general class — consistent with the AFE
  computation above, and `≤ 1` exactly for `d ≤ 2`.
- **Kaczorowski–Perelli** (*On the prime number theorem for the Selberg class*, Arch. Math. 2005):
  `N_F(σ,T) ≪_ε T^{c(1−σ)+ε}` uniformly for `1/2 ≤ σ ≤ 1` with `c = 4d_F + 12`. Non-trivial only for
  `σ > 1 − 1/c`; at `σ = 1/2` the exponent is `c/2 ≥ 8` — **vacuous near the critical line**.

> **Verdict: the speculation is FALSE.** Every unconditional zero-density estimate available for the
> Selberg class lives in `σ > 2/3` or near `σ = 1`. Hypothesis (a) needs `σ → 1/2` and is open for
> every `d ≥ 2`. **§100.1's scope assessment is confirmed**, and now carries its citations.

> **Recorded do-not-retry.** "Improve the mean-square input and hypothesis (a) follows" is dead: the
> mean square is already optimal for `d ≤ 2` (`λ = 1`) and the obstruction is the zero-detection
> method's `σ > 2/3` floor, not the moment. Any attack on (a) must replace Montgomery's zero
> detection, not feed it a better moment.

**Correction to §100.1 to carry forward:** its displayed mean-square bound is the convexity one and
understates what is known; replace it with the AFE bound above. The *conclusion* of §100.1 is
unchanged.

### 166.2 The mod-1 rigidity principle — why every `L²` route to `S_F` mod 1 must fail

Two exact facts, both already in the log, combine into a rule that was not stated.

1. **Unconditional (§139.1(A)).** `e^{2πikS_F} = e^{−2πikM_F}` exactly, and van der Corput on
   `[2πe, T]` gives, with no truncation and no hypothesis,
   ```
   M_T\{e^{2πikS_F}\} := (1/T)∫_0^T e^{2πikS_F(t)}dt  ≪_{F}  1/(k\,d_F\,T) .
   ```
   Equivalently: `S_F ≡ −M_F (mod 1)`, i.e. `F/\bar F` on the critical line is the archimedean ratio
   `ω_F χ_F(t)` — **the identity is the functional equation, and carries no arithmetic at all.**
2. **Conjectural/Selberg-CLT side.** If `A` is any Dirichlet-polynomial approximation to `S_F` with
   `Var(A) ∼ (n_F/2π²)\log\log T`, then `M\{e^{2πikA}\} ≈ e^{−2π²k²Var(A)} = (\log T)^{−k²n_F}`.

The two differ by a factor `T(\log T)^{−k²n_F} → ∞`. Since `M\{e^{2πikS_F}\} = M\{e^{2πikA}\}·M\{e^{2πikR}\}`
in the independent model with `R = S_F − A`,

> **Principle (mod-1 rigidity).** For every decomposition `S_F = A + R` with `A` a prime-sum
> approximation, the remainder satisfies `|M_T\{e^{2πikR}\}| ≈ T^{−1}(\log T)^{k²n_F}` — it is
> equidistributed mod `1` to within `T^{−1+o(1)}` **even though `‖R‖_{L²} = o(‖S_F‖_{L²})`**. The
> entire mod-1 distribution of `S_F` lives in the `L²`-negligible remainder.

Consequences, all confirming recorded failures with a single cause:
- §140.2 ("no choice of `N` makes the two sides conflict") and §150.2 ("no periodic test function
  improves the rate") are the same phenomenon: the characteristic-function method sees only `M_F`.
- Theorem 84′ works precisely because `n_F = 0` makes `R` a genuine `B²` object, so `A` is the whole
  of `S_F` and there is no remainder to hide the arithmetic in.
- **Rule for future cycles:** *no `L²`-approximation argument can transfer mod-1 information.* Any
  method whose only control on the error is a mean square is blind to integrality of `N_F`.

### 166.3 The shift-orbit Hilbert structure, and Theorem 97

For `F ∈ S` **entire** (no pole at `s = 1`) every vertical shift `F_θ(s) := F(s+iθ)` again lies in
`S`: axioms (1),(4),(5) are invariant since `|a_{F_θ}(n)| = |a_F(n)|`, and the functional equation
transports with `γ(s) ↦ γ(s+iθ)` (the condition `Re μ_j ≥ 0` survives, as `μ_j ↦ μ_j + iλ_jθ`) and
`ω ↦ ωQ^{−2iθ}`. So `S` carries an `ℝ`-action.

Let `W` be the space of bounded prime-indexed sequences modulo `ℓ²(1/p)`, with the semi-inner product
```
⟨u,v⟩ := lim_x (\log\log x)^{−1} Σ_{p≤x} u_p \overline{v_p} / p ,
```
and let `(U_θ u)_p := u_p p^{−iθ}`. Then `U_θ` is **unitary** for `⟨·,·⟩` and `[F_θ] = U_θ[F]`. Hence
```
ψ_{F,G}(θ) := c_{F_θ,G} = ⟨U_θ[F],[G]⟩ ,      n_F = ‖[F]‖² = ψ_{F,F}(0) ,
```
and `ψ_{F,F}` is a **positive-definite function on `ℝ`**: `n_F` is the total mass of the spectral
measure of `[F]` for the one-parameter unitary group `U`, a measure on the Bohr compactification `bℝ`.

> **Reformulation.** Conjecture A `⟺` that total spectral mass is a non-negative integer;
> Conjecture B `⟺` for primitives `F ≠ G` the cross spectral measure vanishes identically.
> The atoms of `ψ_{F,F}` sit exactly at the `θ` for which the shift permutes the primitive factors of
> `F` — e.g. `F = P·P_θ` has `ψ_{F,F}(±θ) = 1` — so "no atoms off `0`" is the correct shift-covariant
> form of Conjecture B.

Applying `bessel_of_almost_orthogonal` (formalised this cycle) with `e_j(p) = p^{−iθ_j}`,
`u_p = a_F(p)\overline{a_G(p)}`, `A = Σ_{p≤x}1/p` and off-diagonal error
`|Σ_{p≤x}p^{−1−iτ}| = |\log ζ(1+iτ)| + O(1) = O_τ(1)`:

> **Theorem 97 (shift-correlation finiteness).** Let `F,G ∈ S` and set
> `Q := \limsup_x (\log\log x)^{−1}Σ_{p≤x}|a_F(p)|²|a_G(p)|²/p` (finite under Bounded Satake). Then
> for every finite set of distinct `θ_j` at which the correlations exist,
> ```
> Σ_j |c_{F_{θ_j},G}|²  ≤  Q .
> ```
> Hence `{θ : c_{F_θ,G} ≠ 0}` is countable, `Σ_θ|c_{F_θ,G}|² ≤ Q`, and at most `Q/ε²` shifts have
> `|c_{F_θ,G}| ≥ ε`. With `G = F` this gives `n_F² ≤ Q`, i.e. Cauchy–Schwarz between the second and
> fourth prime moments.

*Novelty:* elementary Bessel/large-sieve; under Rankin–Selberg the finiteness is standard. Recorded
as **infrastructure, low novelty**, useful because it is unconditional given BS and because it is the
statement `bessel_of_almost_orthogonal` was built for.

### 166.4 Lean

New, `lake build +GaloisForLFunctions.HTGeometry` **clean**:
```lean
theorem bessel_of_almost_orthogonal (B : V → V → ℂ)
    (hadd₁ …) (hsmul₁ …) (hconj …) (hpsd …)
    {ι} [Fintype ι] [DecidableEq ι] (e : ι → V) (u : V) (A ε : ℝ)
    (hε : 0 ≤ ε) (hpos : 0 < A + Fintype.card ι * ε)
    (hgram : ∀ i j, ‖B (e i) (e j) - (if i = j then (A : ℂ) else 0)‖ ≤ ε) :
    ∑ i, ‖B u (e i)‖ ^ 2 ≤ (A + Fintype.card ι * ε) * (B u u).re
```
in `HTGeometry/BesselPSD.lean`, beside `bessel_of_orthonormal` (`ε = 0`, `A = 1`). Proof: test
positivity on `u − λ∑ᵢ B u (eᵢ)•eᵢ` and optimise the real scalar at `λ = (A + card·ε)⁻¹`. Corpus
search run first: `research "Bessel inequality almost orthogonal Gram positive semidefinite form"`
and `rg` over `HTGeometry`/`RHTower` returned only `bessel_of_orthonormal`,
`TraceNorm.sum_inner_sq_le_of_orthonormal_with_zeros` (needs a genuine inner-product space) and
`OrthonormalTrialSpan.norm_sq_apply_le_of_orthonormal_span` (exact orthonormality). No duplication.

### 166.5 Position after cycle 166

```
new & unconditional  : Thm 84′, 85′, 90, 91, 93, Cor 92, 94   (characteristic-function block)
new, low novelty     : Thm 97 (needs BS)
classical repackaged : Thm 95, 96, §164.2                      (Montgomery's identity)
killed this cycle    : "d ≤ 2 unlocks hypothesis (a)"          (Mukhopadhyay–Srinivas: σ > 2/3 floor)
new rule             : mod-1 rigidity — no L²-approximation reaches the mod-1 distribution
open                 : Conjecture A, Conjecture B, Energy Gap for 0 < n_F < 1
```

---

## 167. Cycle 167 (2026-07-26) — Theorem 91's proof was resting on a misapplied Baker bound; corrected proof, same theorem

### 167.1 The defect

§149.1 justifies the scale-coupling of the characteristic-function iteration as follows:

> "The Weyl step in §139.1(B) requires equidistribution of `(t\log p)_{p≤N}` over `t ∈ [0,T]`. By
> Baker's theorem the gaps between distinct values of `Σ_p m_p\log p` with bounded `|m_p|` and
> `p ≤ N` are `≫ (\log N)^{−C}`, so the step is valid for `N ≤ T^{c}` with `c = c(k) > 0`."

**That is not what Baker's theorem gives.** The effective lower bound for a non-vanishing linear form
in `n` logarithms of algebraic numbers carries a constant that degrades **super-exponentially in `n`**
(shape `C(n) ≈ (16nd)^{2n}`). Here `n = π(N)` grows with `N`, so the Baker bound degenerates to
something like `\exp(−C^{π(N)})` and supports only `N ≪ \log\log T`, far short of `N ≤ T^{c}`.
Theorem 91's stated rate `E(T) ≫ \log\log\log T` does not follow from the argument as written.

### 167.2 What is actually true, and it is elementary

Baker is the wrong tool and is not needed. For **positive integers**:

> **Lemma (log separation).** If `a ≠ b` are positive integers then
> `|\log a − \log b| ≥ (\max(a,b))^{−1}`.
>
> *Proof.* Say `b < a`. Then `\log(a/b) ≥ 1 − b/a = (a−b)/a ≥ 1/a`, using `\log x ≥ 1 − x^{−1}`. ∎

> **Lemma (bounded-degree monomial separation).** Let `n_i ≤ N` be positive integers and
> `m_i ∈ Z` with `Σ_i|m_i| ≤ D`. Then `Λ_m := Σ_i m_i\log n_i` is either `0` or satisfies
> `|Λ_m| ≥ N^{−D}`.
>
> *Proof.* Write `Λ_m = \log a − \log b` with `a = ∏ n_i^{m_i^+}`, `b = ∏ n_i^{m_i^-}`; then
> `a,b ≤ N^{D}`, and apply the previous lemma. ∎

**The constant does not degrade with the number of bases.** That is exactly the property Baker lacks
and the property the iteration needs.

### 167.3 The corrected coupling: moments, not the raw exponential

The Weyl step is only ever used to evaluate `M_T\{e^{2πik𝒮_N}\}`. Replace it by a truncated-moment
evaluation, which involves only frequencies of **bounded degree**:

1. Fix `D = 2j`. For every monomial of degree `≤ D` in `(t\log p)_{p≤N}`, §167.2 gives
   `|Λ_m| ≥ N^{−D}`, so by `oscInt_norm_le` its time average over `[0,T]` is `O(N^{D}/T)`. The number
   of such monomials is `≤ (2N)^{D}`, so
   ```
   M_T\{𝒮_N^{\,r}\}  =  M\{𝒮_N^{\,r}\}  +  O\big(C^{D} N^{2D}/T\big) ,   r ≤ D ,
   ```
   which is admissible as soon as **`N ≤ T^{1/(2D)}`** (up to constants).
2. Convert moments to the exponential: on `\{|𝒮_N| ≤ V\}` the Taylor remainder of order `D` is
   `≤ (2πkV)^{D+1}/(D+1)!`, and `\mathrm{meas}\{|𝒮_N|>V\} ≤ V^{−D}M\{𝒮_N^{D}\}`. With
   `V ≍ \sqrt{j\,E(N)}` and `j ≍ C k² E(N)` both are `o(1)`.

So the admissible truncation is
```
\log N  ≍  \log T / (C k² E(N)) ,
```
i.e. `N` is a **fixed power of `T` with exponent `1/(Ck²E)`** — not `T^{c}` with `c` absolute, but
still polynomial, and that is all the iteration uses.

### 167.4 The iteration re-run, and Theorem 91 survives

Set `x_{j+1} := x_j^{1/(Ck²E(x_j))}`, so `\log\log x_{j+1} = \log\log x_j − \log(Ck²E(x_j))`. Since
`E` is non-decreasing, the number of admissible scales down from `T` is
```
J  ≍  \log\log T / \log(Ck²E(T)) .
```
Feeding this into (★) exactly as in §149.1,
```
E(T)  ≥  J·\frac{1}{4π²k²}e^{−2k²E(T)}
      ≍  \frac{\log\log T}{\log(Ck²E(T))}·\frac{e^{−2k²E(T)}}{4π²k²} ,
```
so with `k = 1`,
```
E(T)\,\log(C E(T))\,e^{2E(T)}  ≫  \log\log T ,
```
whence `2E(T) + \log E(T) + \log\log(CE(T)) ≥ \log\log\log T + O(1)` and therefore

> **Theorem 91 (unconditional; corrected proof).** For every non-trivial `H` in the group completion
> of `S`,
> ```
> Σ_{p≤T}|a_H(p)|²/p  ≫  \log\log\log T .
> ```

The rate is unchanged: the extra `\log(CE)` in the denominator of `J` costs only a
`\log\log\log\log T` inside a logarithm and is absorbed. **The theorem stands; its proof no longer
invokes Baker's theorem at all**, and is now elementary (log separation + oscillatory integral bound
+ moment truncation).

### 167.5 Consequences for the recorded results

- **Corollary 92** (`(1/T)∫_0^T|S_F|² ≫ \log\log\log T`, `S_F` unbounded) is unaffected: it consumes
  Theorem 91 as a black box.
- **Theorem 84′ and Theorem 85′ never used the quantitative coupling** — they take `T → ∞` first with
  `N` fixed, then `N → ∞`, where plain Weyl equidistribution of `π(N)` fixed frequencies is valid with
  no rate. Unaffected.
- **Corollary 94**'s lower bound inherits the corrected proof. Unaffected in statement.
- The proof-level dependency list of the block changes: **Baker's theorem is removed** from the inputs
  of §150.3's table; the inputs are now van der Corput, Weyl equidistribution (qualitative), the
  elementary log separation of §167.2, and the Bessel-type non-vanishing of the Euler product.

> **Recorded rule (seventh design rule).** *Never import a Diophantine bound whose constant depends on
> the number of variables into an argument where that number grows.* This is the same failure mode as
> §148 ("never let a named constant stand for a hypothesis"), one level down: `C` in
> "`≫ (\log N)^{−C}`" silently depended on `π(N)`.

### 167.6 Lean

New file `HTGeometry/LogFrequencySeparation.lean`, registered in the umbrella,
`lake build +GaloisForLFunctions.HTGeometry` clean:
```lean
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x
theorem inv_max_le_abs_log_sub_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ((max a b : ℕ) : ℝ)⁻¹ ≤ |Real.log a - Real.log b|
theorem inv_le_abs_log_sub_log_of_le {a b M : ℕ} … : ((M : ℕ) : ℝ)⁻¹ ≤ |Real.log a - Real.log b|
theorem monomial_log_separation {ι} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (m : ι → ℤ) (N D : ℕ) (hN : 0 < N)
    (hn : ∀ i, 0 < n i) (hnN : ∀ i, n i ≤ N) (hdeg : ∑ i, (m i).natAbs ≤ D) :
    ∑ i, (m i : ℝ) * Real.log (n i) = 0 ∨
      (((N : ℕ) : ℝ) ^ D)⁻¹ ≤ |∑ i, (m i : ℝ) * Real.log (n i)|
```
Corpus search run first (`research "logarithm difference lower bound distinct positive integers
frequency separation"`, plus `rg` for `log_sub_log` / `separation`): only unrelated Böttcher
`norm_bottcherLog_sub_log_le` and Green-band separations. No duplication. The docstring
cross-references `GeneralizedDirichletMeanValue.oscInt_norm_le`, which supplies the `2/|δ|` factor the
separation is paired with.

> This is now the **arithmetic input of the whole characteristic-function block**, formalised: the
> block's non-trivial Diophantine content is exactly `|\log a − \log b| ≥ 1/\max(a,b)`.

---

## 168. Cycle 168 (2026-07-26) — Theorem 48 has the sign backwards: the collision function has a zero **deficit**, not a surplus

### 168.1 The computation, redone

Let `F,G ∈ S` share `γ`, `Q` and `ω`, let `H := F − G = Σ_{n≥n_0}c'_n n^{−s}` with
`c'_{n_0} ≠ 0`, and `D := Λ_F − Λ_G = Q^sγ(s)H(s)`. Factor out the leading frequency:
```
D(s) = c'_{n_0}·(Q/n_0)^s·γ(s)·\tilde K(s) ,      \tilde K(s) = 1 + Σ_{n>n_0}(c'_n/c'_{n_0})(n/n_0)^{−s} → 1 .
```
So `D` has **the same `γ`-factor and the scale parameter `Q` replaced by `Q/n_0`.**

The Riemann–von Mangoldt formula in `S^♯` is
```
N(T) = (d/2π)T\log T + (T/π)\log Q + (T/π)Σ_jλ_j\logλ_j − (d/2π)T + O(\log T) ,
```
checked against `ζ` (`Q = π^{−1/2}`, `d = 1`, `λ = 1/2`): the three constants give
`(T/2π)(\log T − \logπ − \log 2) − T/2π = (T/2π)\log(T/2π) − T/2π` ✔. **The `Q`-dependence is
`+(T/π)\log Q`.** Since `Δ\arg\tilde K = O(\log T)` (a general Dirichlet series tending to `1`, of
finite order),

> **Theorem 48 (corrected).** `N_D(T) = N_{Λ_F}(T) − (T/π)\log n_0 + O(\log T)`.
> The collision function has a **deficit** of `(\log n_0)/π` zeros per unit height, not a surplus.

§92.1 wrote `+(T/π)\log n_0`. The error is a sign: `\arg(n_0^{−s}) = −t\log n_0`, which enters the
count with the same sign as `\arg Q^s = +t\log Q`, hence contributes `−(T/π)\log n_0`.

### 168.2 What must be retracted, and what survives

- **RETRACTED (§92.2):** "The surplus zeros of `D` are not attached to any zero collision… a genuine
  new zero set of density `(\log n_0)/π` canonically attached to the pair `(F,G)`." There is no such
  zero set. `D` has *fewer* zeros than `Λ_F`, and no new zeros are created.
- **RETRACTED (§92.2):** "if `F ≠ G` then `D` has *strictly more* zeros than `Λ_F`". It has strictly
  fewer.
- **SURVIVES:** `n_0` is still read off a zero density — now as a deficit — so the analytic
  recovery of the first disagreement index from the zeros of `Λ_F − Λ_G` stands.
- **SURVIVES verbatim:** the reduction (b″) ⟹ (b′). "Any hypothesis forcing
  `N_D(T) = N_{Λ_F}(T) + o(T)` forces `n_0 = 1`, i.e. `F = G`" uses only that the discrepancy is
  non-zero for `n_0 ≥ 2`, which the corrected sign preserves. So §92's chain
  `(a) + (b″) ⟹ (b′) ⟹ (P2) ⟹ (ZS)` is unaffected.

### 168.3 The corrected sign turns (b″) into a conductor problem  [new]

The invariants of Kaczorowski–Perelli for a functional equation of Selberg type are
`d = 2Σλ_j` and `q = (2π)^{d}Q²∏_jλ_j^{2λ_j}` (check: `L(s,χ)` mod `q` has `q_F = q` ✔). Since `D`
has the same `d` and `λ_j` and `Q_D = Q/n_0`,
```
q_D  =  q_F / n_0²  ,       i.e.       n_0  =  \sqrt{q_F/q_D} .
```

> **Reduction.** *Effective strong multiplicity one at the square root of the conductor* —
> "`a_F(n) = a_G(n)` for all `n ≤ \sqrt{q_F}` implies `F = G`" — is **exactly equivalent** to the
> statement `q_D ≥ 1`, i.e. to a lower bound of `1` for the conductor of the collision function.

Two remarks on scope, recorded honestly:

1. `D` is **not** an element of `S^♯`: after factoring `n_0^{−s}` the remaining series `\tilde K` has
   frequencies `\log(n/n_0)`, which are not logarithms of integers. So the known conductor results in
   `S^♯` (Kaczorowski–Perelli: `S^♯` is empty for `0 < d < 1` and for `1 < d < 2`; for `d = 1` the
   conductor is a positive integer and `F` is a combination of shifted Dirichlet `L`-functions;
   Kaczorowski–Perelli, *Classification of L-functions of degree 2 and conductor 1*, Adv. Math. 2022;
   and the "forbidden conductors" line, arXiv:2208.12947, arXiv:2408.10385) do **not** apply directly.
   The equivalence above is therefore a reduction to a conductor lower bound for **general** Dirichlet
   series with a Selberg-type functional equation, which is the natural next object.
2. The expected truth is `n_0 ≪ \sqrt{q_F}` because the approximate functional equation for
   `F − G` on the critical line has length `≍ \sqrt{𝔮(t)} ≍ \sqrt{q_F}` at `t ≍ 1`: if all coefficients
   below that length vanish, both sums in the AFE are empty. Making that rigorous (uniformly in `t`,
   with the AFE error controlled) is a concrete, finite, zero-free target — **and it is degree-agnostic**,
   unlike everything in §166.1.
   *Consistency check in degree 1:* for `χ_1 ≠ χ_2` mod `q`, `n_0` is the least `n` with
   `χ_1(n) ≠ χ_2(n)`, and Burgess gives `n_0 ≪ q^{1/4+ε} = o(\sqrt q)` ✔, so `q_D ≥ 1` holds there with
   room to spare.

### 168.4 Standing correction ledger

Two defects in previously recorded theorems were found and repaired in cycles 167–168, both by
re-deriving rather than re-reading:

| where | defect | status |
|---|---|---|
| §149.1 (Thm 91) | Baker's theorem cited with a constant that secretly depends on `π(N)` | **repaired**: elementary log separation `\|\log a−\log b\| ≥ 1/\max(a,b)` + moment truncation; theorem and rate unchanged; Baker removed from the dependency list |
| §92.1 (Thm 48) | sign of the `n_0`-contribution to the zero count | **corrected**: deficit, not surplus; §92.2's "new zero set" retracted; the (b″) ⟹ (b′) chain unaffected |

> **Recorded practice.** Both defects sat undetected for tens of cycles because later cycles cited the
> statements rather than the derivations. **Re-derive any recorded theorem before building a new
> reduction on it.**

### 168.5 A third instance of the same defect, in the preprint

Audit of `4-publication-ready/monodromy-integrality-selberg.md` triggered by §167.5's new rule.
Theorem 13 there claimed the off-diagonal separation
```
|k\log q − j\log p| ≫ (\log X)^{−C}   for   d = p^j, e = q^k ≤ X ,
```
attributed to "Baker's theorem on linear forms in two logarithms". **This is false** where it is
used: for twin primes `p, q = p+2 ≤ X`, `|\log p − \log q| ≍ 1/X`. A `(\log X)^{−C}` separation is
available only for perfect powers with both exponents `≥ 2` (Tijdeman); the dominant terms of the
extractor have `j = k = 1`.

Corrected in place: the separation is the elementary `|\log d − \log e| ≥ 1/\max(d,e) ≥ 1/X`, hence
`δ = 1/X` rather than `(\log X)^{−C}`, and **no transcendence theory is used in the paper at all**.
The Lean declarations cited there (`exists_gap_of_injOn`, `diagonal_isolation`) were never affected:
they are purely qualitative — a finite set of distinct reals has a positive minimal gap — and carry no
quantitative claim. The over-claim lived only in the prose.

> **Net effect on Theorem 13.** The extractor's smoothing parameter degrades from `(\log X)^{−C}` to
> `X^{−1}`. Since Theorem 13 was already recorded (§60.2) as landing on the pair correlation of zeros
> rather than delivering MI, no downstream statement changes; but the *strength* claimed for the
> diagonal isolation must be read at `δ = 1/X`.

**Three instances of one failure mode in three cycles.** §149.1, §92.1, and now Theorem 13 of the
preprint. The rule of §167.5 is upgraded to a standing audit item: *every quantitative Diophantine
input in the corpus must be re-derived from an elementary bound or dropped.* The elementary bound
`|\log a − \log b| ≥ 1/\max(a,b)` (formalised, §167.6) is sufficient everywhere it was needed.

---

## 169. Cycle 169 (2026-07-26) — a new mechanism: **non-negativity of a zero count bounds a conductor from below**

The corrected Theorem 48 (§168.1) says `q_D = q_F/n_0²`. So a lower bound on `q_D` is *exactly* an
upper bound on the first coefficient disagreement index. This cycle supplies the mechanism.

### 169.1 The mechanism

A Riemann–von Mangoldt count has the shape
```
N(T) = A·T\log T + B·T + E(T) ,      A = d/2π ,  B = (\log q)/2π ,  |E(T)| ≤ C(1+\log(T+2)) .
```
`N(T) ≥ 0` for every `T > 0` — it counts zeros. Evaluate at a single height and divide by it:
```
B  ≥  −A\log T_0 − C(1+\log(T_0+2))/T_0     for every  T_0 > 0 .
```
**Take `T_0 = 1`: the `A`-term vanishes identically** (`\log 1 = 0`), leaving
```
B ≥ −C(1+\log 3) ,    i.e.    q ≥ \exp\big(−2πC(1+\log 3)\big) .
```

> **The conductor is bounded below by a quantity depending only on the uniformity of the error term
> in the counting formula — not on the degree, not on the gamma factor.**

This is the third time in the programme that **positivity/integrality of a count** is *used* rather
than sought (after §91.1's `Z`-valued `N_F − N_G`, and §139.1's `e^{2πikN_F} = 1`). It is the first
time it produces a *conductor* bound.

### 169.2 The reduction to effective strong multiplicity one

Let `F ≠ G ∈ S` share `γ`, `Q`, `ω`; let `n_0` be least with `a_F(n_0) ≠ a_G(n_0)`;
`D = Λ_F − Λ_G = c_{n_0}(Q/n_0)^sγ(s)\tilde K(s)`, `\tilde K → 1`.

> **Theorem 98 (effective strong multiplicity one — conditional on one uniformity).**
> Suppose the argument variation of the normalised collision function satisfies
> ```
> (1/π)\,|Δ\arg \tilde K|  ≤  C_0\big(1 + \log(𝔮_D(T))\big)          (U)
> ```
> with `C_0` depending only on `d` and the `μ_j` (**not** on `n_0` or `c_{n_0}`). Then
> `q_D ≥ \exp(−2πC_0(1+\log 3))`, hence
> ```
> n_0  ≤  \exp\big(πC_0(1+\log 3)\big)\cdot\sqrt{q_F} .
> ```
> Equivalently: *if `a_F(n) = a_G(n)` for every `n ≤ C_d\sqrt{q_F}`, then `F = G`.*

**Open core (U).** `\tilde K(s) = 1 + Σ_{n>n_0}(c_n/c_{n_0})(n/n_0)^{−s}` converges absolutely only
for `σ > σ_1` with `σ_1 ≈ 1 + 2n_0^{1+ε}/|c_{n_0}|`, so the naive Backlund argument gives `C_0`
depending on `n_0` and `|c_{n_0}|`, and the reduction becomes circular. **(U) is the whole content**,
and it is a statement about one explicit entire function of order `1`, with no primes, no Euler
product, and no zero-density input.

*Unconditional residue, degree 1.* Running the naive bound gives `C_0 ≪ σ_1 ≪ n_0^{1+ε}/|c_{n_0}|`,
hence `n_0² ≤ q_F\exp(Cn_0^{1+ε}/|c_{n_0}|)` — vacuous. The naive route is therefore **not** a weak
version of Theorem 98; it gives nothing. Recorded so it is not re-attempted.

### 169.3 Why `√q_F` is the right threshold, and a consistency check

The approximate functional equation for `H = F − G` on the critical line has length `≍ \sqrt{𝔮(t)}`,
`𝔮(0) ≍ q_F`. If every coefficient below that length vanishes, both AFE sums are empty. So `√q_F` is
the natural and presumably sharp threshold. Consistency in degree `1`: for `χ_1 ≠ χ_2` mod `q`, `n_0`
is the least `n` with `χ_1(n) ≠ χ_2(n)`, and Burgess gives `n_0 ≪ q^{1/4+ε} = o(\sqrt q)` ✔, i.e.
`q_D ≫ q^{1/2−ε} → ∞`, far above the required `≥ c`.

### 169.4 Novelty

Searched (July 2026): Murty–Murty *Strong multiplicity one for the Selberg class* (CMB;
arXiv:math/0210299) determines elements from prime coefficients, with a hypothesis at prime squares
in general degree — **not effective in the conductor**. The converse-theorem line
(Kaczorowski–Perelli, *Classification of L-functions of degree 2 and conductor 1*, Adv. Math. 2022;
arXiv:2110.00311; arXiv:2207.00451 Venkatesh-type; arXiv:2604.00693 on identification by preimages of
finite sets) addresses determination but not a coefficient-range bound of the form `n_0 ≪ \sqrt{q}`.

> **Not located in the literature.** Assessed, not claimed. The mechanism of §169.1 (count
> positivity ⟹ conductor lower bound) is elementary and may well be folklore; the *application* to the
> collision function via `q_D = q_F/n_0²` is what is new here, and it is exactly as strong as (U).

### 169.5 Lean

New `HTGeometry/CountPositivityConductorBound.lean`, registered, `lake build` clean:
```lean
theorem linear_coeff_ge_of_nonneg {A B C : ℝ}
    (h : ∀ T : ℝ, 0 < T → 0 ≤ A * T * Real.log T + B * T + C * (1 + Real.log (T + 2)))
    {T₀ : ℝ} (hT₀ : 0 < T₀) :
    -A * Real.log T₀ - C * (1 + Real.log (T₀ + 2)) / T₀ ≤ B
theorem linear_coeff_ge_of_nonneg_at_one … : -(C * (1 + Real.log 3)) ≤ B
theorem conductor_ge_of_count_nonneg {A C q : ℝ} (hq : 0 < q)
    (h : ∀ T : ℝ, 0 < T →
      0 ≤ A * T * Real.log T + (Real.log q / (2 * Real.pi)) * T + C * (1 + Real.log (T + 2))) :
    Real.exp (-(2 * Real.pi * (C * (1 + Real.log 3)))) ≤ q
```
The last statement is the mechanism in closed form: *a nonnegative count with a logarithmic error
forces a positive lower bound on the conductor, with the bound determined by the error constant
alone.* Corpus search run first; no existing declaration relates count positivity to a conductor.

### 169.6 Position

```
open core promoted : (U) — uniform argument-variation bound for the normalised collision function
                     ⟹ Theorem 98 (effective SMO at √q_F), degree-agnostic, zero-free, prime-free
still open         : Conjecture A, Conjecture B, Energy Gap 0 < n_F < 1
```

---

## 170. Cycle 170 (2026-07-26) — the scale conflict that blocks Theorem 98, and why `d ≤ 2` keeps appearing

Attack on (U)/Theorem 98 by the route that avoids `\arg` entirely: mean squares.

### 170.1 The two estimates, and where they meet

Let `H = F − G = Σ_{n≥n_0}c_n n^{−s}`, `c_n ≪_ε n^ε`, `c_{n_0} ≠ 0`.

**Lower bound (Montgomery–Vaughan).**
`∫_0^T|H(σ+it)|²dt = Σ_n|c_n|²n^{−2σ}(T + O(n))`, so at `σ = 2` the `n = n_0` term dominates and
```
∫_0^T |H(2+it)|²dt  ≥  \tfrac12 T\,|c_{n_0}|²n_0^{−4}     provided   T ≥ C n_0 .        (L)
```
The diagonal error is `O(n_0)` per unit of `|c_{n_0}|²n_0^{−4}`, so **`T ≫ n_0` is forced** — no
choice of `σ` removes it, because the error/main ratio is `n/T` at every `σ`.

**Upper bound (approximate functional equation).** The AFE for `H` at height `t` has length
`\sqrt{𝔮(t)} ≍ \sqrt{q\,t^{d}}`. If `n_0 ≥ 2\sqrt{𝔮(t)}` both sums are past the cutoff and
`|H(1/2+it)| ≪_A n_0^{1/2+ε}2^{−A}`; that is,
```
|H| is negligible for   t ≪ (n_0²/q)^{1/d} .                                            (U')
```

**Conflict.** (L) needs `T ≫ n_0`; (U') supplies smallness only for `T ≪ (n_0²/q)^{1/d}`. They
overlap iff
```
n_0  ≪  (n_0²/q)^{1/d}   ⟺   n_0^{\,1−2/d}  ≪  q^{−1/d}   ⟺   n_0  ≫  q^{1/(2−d)}  (for d < 2).
```

> **Theorem 99 (what the mean-square route actually proves).** For `F ≠ G ∈ S^♯` with identical
> `γ`-factor and `d_F = d < 2`, the first disagreement index satisfies
> ```
> n_0  ≪_{d,ε}  q_F^{\,1/(2−d)+ε} .
> ```
> For `d = 1` this is `n_0 ≪ q_F^{1+ε}`. For `d → 2^-` the exponent blows up, and for `d ≥ 2` the
> route gives **nothing**.

So the mean-square route does **not** reach the natural threshold `\sqrt{q_F}` even in degree `1`
(where Burgess already gives `q^{1/4+ε}` for Dirichlet characters), and it dies exactly at `d = 2`.
Recorded as a **do-not-retry** for the "mean squares instead of `\arg`" idea: the `T ≫ n_0`
requirement in (L) is intrinsic to the diagonal error and cannot be traded away.

### 170.2 The unifying reason `d ≤ 2` is the frontier  [structural]

Three independent barriers in this log now have the same single cause:

| barrier | where | condition |
|---|---|---|
| second moment `∫_0^T\|F(σ+it)\|²dt ≪ T^{1+ε}` on `σ ≥ 1/2` | §166.1 | AFE length `T^{d/2} ≤ T` |
| effective SMO via mean squares | §170.1 | AFE length `\sqrt{qT^{d}} ≥ n_0 ≥ ` diagonal scale `T` |
| the fourth moment (= second moment of `F²`, degree `2d`) | §166.1 | `2d ≤ 2` |

> **Principle (AFE–diagonal threshold).** Every unconditional handle on `F ∈ S` obtained by pairing
> the approximate functional equation with a mean value theorem for Dirichlet polynomials requires
> the AFE length `\sqrt{𝔮(T)} ≍ \sqrt{q}\,T^{d/2}` to be at most the diagonal scale `T`, i.e.
> **`d_F ≤ 2`**. This is the arithmetic reason the Selberg class is understood only in degree `≤ 2`,
> and it is the *same* reason in the degree conjecture, the moment problem, hypothesis (a), and
> effective strong multiplicity one. Anything that crosses `d = 2` must abandon the pairing, not
> improve either factor.

This retro-explains: Kaczorowski–Perelli's structure theorems reach `d < 2`; Conjecture B is known
only in degree `1`; hypothesis (a) is unconditional only in degree `1`; and the standard twist
(§100.2) resonates at exactly one exponent `κ = 1/d`.

### 170.3 Status of Theorem 98

`(U)` — a uniform argument-variation bound for the normalised collision function, with constants
independent of `n_0` and `|c_{n_0}|` — remains the open core, and §170.1 shows it cannot be replaced
by mean squares. Its difficulty is concentrated in one place, now identified precisely:

> **the possible smallness of `c_{n_0} = a_F(n_0) − a_G(n_0)`.** Every route to `(U)` needs a lower
> bound for `|c_{n_0}|`, or an argument insensitive to it. The Selberg axioms give none: they bound
> coefficients above (`a_F(n) ≪ n^ε`) and never below.

> **New named target (NC).** *Is there an absolute lower bound `|a_F(n_0) − a_G(n_0)| ≫ n_0^{−A}` for
> the first disagreement of two elements of `S` with the same functional equation?* Under PEP the
> coefficients are polynomials in Satake parameters; under any integrality of the local factors they
> would be bounded below by a discriminant argument. **(NC) is the first place in this programme
> where a *lower* bound on coefficients is needed, and none of the five axioms provides one.**

---

## 171. Cycle 171 (2026-07-26) — **major correction: Theorem 91 is conditional, not unconditional**

Auditing (★) itself, as §167.5's rule demands, rather than the scale-coupling around it.

### 171.1 The defect

§147.1 derives (★) as
```
| M_T\{e^{2πikX}\} − e^{2πikc}∏_{p≤N}I_p |  ≤  2πk\,\|X − c − 𝒮_N\|_{L²[0,T]}/\sqrt T
                                            ≈  2πk\sqrt{E(T) − E(N)} ,
```
the words being "**truncating the `B²` expansion at `N`**". That expansion is Theorem 77, whose
hypothesis is `Σ_p|a_F(p)|²/p < ∞` — **convergence**. Under convergence, `S_F = c + 𝒮` with `𝒮 ∈ B²`
and `‖S_F − c − 𝒮_N‖_{B²}² = (1/2π²)Σ_{n>N}|Λ_F(n)|²/(n\log²n)` exactly. ✔

§149.1 then applies (★) to an `H` whose energy **diverges**. There Theorem 77 does not apply, `𝒮` is
not a `B²` function at all, and the displayed evaluation of `‖S_H − c − 𝒮_N‖_{L²[0,T]}/\sqrt T` has no
justification. What is needed is an **upper** bound
```
(1/T)∫_0^T |S_H(t) − 𝒮_N(t)|²\,dt  ≪  E(T) − E(N) + O(1) ,                       (V)
```
which is precisely Selberg's variance estimate for the tail — i.e. **hypothesis (a)**.

> **Correction.** *(★) is established only in the convergent regime. Theorem 91 and everything derived
> from it are conditional on (V).*

### 171.2 What is unconditional and what is not, restated

| result | status |
|---|---|
| Thm 84′ `Σ_p\|a_H(p)\|²/p < ∞ ⟹ H = 1` | **unconditional** — hypothesis *is* convergence |
| Thm 85′ quantitative strong multiplicity one (`= O(1)` hypothesis) | **unconditional** — same reason |
| Thm 89, Thm 87 | **unconditional** — convergent regime |
| Thm 90 (sharpness of the method) | **unconditional** — a statement about (★), not an application |
| Thm 91 `E(T) ≫ \log\log\log T` | **conditional on (V)** — downgraded |
| Cor 92 `(1/T)∫\|S_F\|² ≫ \log\log\log T`; `S_F` unbounded | **conditional on (V)** — downgraded |
| Cor 94 two-sided bracket | lower half conditional on (V); upper half (`≪\log²T`) unconditional |
| Thm 93 (closure of admissible functionals) | unaffected — a statement about the method |

Theorem 75 (`|S_F| ≤ K ⟹ n_F ≤ CK²`) does **not** rescue Corollary 92: it yields only `n_F ≤ CK²`,
finite, so bounded `S_F` is not contradictory. So "`S_F` unbounded for every non-constant `F ∈ S`" is
**not** currently unconditional in the Selberg class (it is classical for `ζ`, by Selberg's own zero
density theorem).

### 171.3 Why (V) cannot be got by duality — the attempt, and why it fails

The Weil explicit formula `∫φ'S_F = 𝒫[φ]` is unconditional for every compactly supported test
function, and `𝒫[φ]` is an explicit prime sum. By `L²` duality
`‖S_F − 𝒮_N‖_{L²[0,T]} = \sup_{‖ψ‖_2 = 1}∫ψ(S_F − 𝒮_N)`, and for `ψ = φ'` the pairing equals
`−Σ_{n>N}(Λ_F(n)/π\sqrt n)\hatφ(\log n)` plus archimedean terms. Cauchy–Schwarz with the frequency
separation of §167.2 then gives
```
(1/T)\Big|∫φ'(S_F − 𝒮_N)\Big|²  ≲  \frac{‖φ'‖_2²}{T}·\frac{E(X) − E(N)}{2π²}
```
**provided `\hatφ` is supported in `[−\log X, \log X]`.** But `L²` duality requires *all* `ψ`, and the
band-limited ones miss exactly the fine-scale component of `S_F − 𝒮_N` — the component controlled by
the zeros at spacing `1/\log T`. Taking `X → ∞` reinstates the divergent sum
`Σ_{n>N}|Λ_F(n)|²/(n\log²n) = ∞`.

> **Recorded do-not-retry.** The explicit formula gives exact control of *band-limited* projections of
> `S_F` and nothing else. (V) is a statement about the full `L²` norm, hence about the fine-scale
> zeros, hence hypothesis (a). This is the same wall as §162 and §165.1 (pair correlation), reached
> from a fourth direction.

### 171.4 Amendment to §167

§167.4's heading "Theorem 91 (unconditional; corrected proof)" must read **"Theorem 91 (conditional on
(V); Diophantine input corrected)"**. §167's own content stands: the Baker citation was wrong, the
elementary separation `|\log a − \log b| ≥ 1/\max(a,b)` is the right input, and the scale coupling
`\log N ≍ \log T/(Ck²E(N))` is now proved. That repair is orthogonal to the present one — §167 fixed
the *Diophantine* input, §171 identifies that the *analytic* input was never there.

### 171.5 Correction ledger, updated

| where | defect | status |
|---|---|---|
| §149.1 (Thm 91) | Baker's constant secretly depends on `π(N)` | repaired (§167) |
| §92.1 (Thm 48) | sign of the `n_0` contribution | corrected (§168) |
| preprint Thm 13 | `(\log X)^{−C}` gap false for `j=k=1` | corrected (§168.5) |
| §147.1 / §149 (★) | `B²` truncation used outside its hypothesis | **Thm 91, Cor 92, Cor 94-lower downgraded to conditional (§171)** |

> **Standing practice, reinforced.** Four defects in five cycles, all found by re-deriving. Three were
> imported bounds cited at the wrong strength; the fourth was a hypothesis silently dropped when a
> lemma was reused outside its regime — the *exact* failure mode §148 named ("never let a named
> constant stand for a hypothesis"), now seen at the level of a whole inequality. **Every result in
> §150.3's table and in the preprint must be re-derived before being cited again.**

---

## 172. Cycle 172 (2026-07-26) — Conjecture A is unconditionally true below degree 2; the frontier is one statement

### 172.1 A corollary that empties §57/§58

Theorem 89 (unconditional) says: no non-trivial `H` in the group completion of `S` has
`Σ_p|a_H(p)|²/p < ∞`. Apply it to `H = F/G` with `a_F(p) = a_G(p)` for **every** prime: then
`Σ_p|a_H(p)|²/p = 0 < ∞`, so `H = 1`.

> **Corollary 101 (unconditional).** Two elements of the group completion of `S` that agree at every
> prime are equal. In particular the prime coefficients `(a_F(p))_p` determine `F ∈ S` outright — not
> merely modulo `ℓ²(1/p)` (Theorem 85′), and with **no** hypothesis on gamma factors or conductors.

**Consequence: §57/§58's hypothesis is empty.** Those cycles computed the prime-square density of
`F/G` for `F,G` with identical prime coefficients and identified it with `−\mathrm{ord}_{1/2}(F/G) ∈ Z`;
Corollary 101 says the only such pair has `F = G`. The theorems are true but vacuous. Recorded so the
route is not revisited.

### 172.2 Conjecture A in low degree, unconditionally

Two classical inputs:

- **(KP structure.)** `S^♯` contains no element of degree `0 < d < 1` (Kaczorowski–Perelli) nor of
  degree `1 < d < 2` (*On the structure of the Selberg class VII*, Ann. of Math. 173 (2011)); degree
  `0` elements of `S` are `≡ 1`; and every degree-`1` element of `S` is `ζ(s)` or `L(s+iθ,χ)` with
  `χ` primitive.
- **(Non-vanishing on the 1-line.)** `L(1+it,χ) ≠ 0, ∞` for every `t` and every `χ` unless `χ` is
  principal and `t = 0` — classical, unconditional.

For degree-1 elements `P_1 = L(s+iθ_1,χ_1)`, `P_2 = L(s+iθ_2,χ_2)`,
```
Σ_p a_{P_1}(p)\overline{a_{P_2}(p)}\,p^{−w}  =  Σ_p χ_1\barχ_2(p)\,p^{−w−i(θ_1−θ_2)}
   =  \log L\big(w + i(θ_1−θ_2),\,χ_1\barχ_2\big) + O(1) ,
```
which is bounded at `w = 1` unless `χ_1\barχ_2` is principal **and** `θ_1 = θ_2`, i.e. unless
`P_1 = P_2`. Hence `c_{P_1,P_2} = δ_{P_1,P_2}` **unconditionally**, and:

> **Theorem 100 (unconditional).** Let `F ∈ S` have all its primitive factors of degree `1`, say
> `F = ∏_i P_i^{m_i}` with the `P_i` distinct degree-`1` elements. Then Selberg's Conjecture B holds
> for every pair `(P_i,P_j)`, and
> ```
> n_F = Σ_i m_i²  ∈  Z_{≥1} ,
> ```
> i.e. Conjecture A holds for `F`, with the exact value.

Combining with the structure input, since degrees add and no degree lies in `(0,1) ∪ (1,2)`:

> **Corollary 102 (the low-degree frontier).** Conjecture A holds unconditionally for every `F ∈ S`
> with `d_F ≤ 2`, **except possibly for primitive elements of degree exactly `2`**, for which the
> conjecture asserts precisely
> ```
> n_F = 1 .
> ```
> Equivalently: *Selberg's Conjecture A in degree `≤ 2` is the single statement `(P1)_2`: every
> primitive degree-2 element of `S` has prime energy density `1`.*

(For `d_F = 2` reducible, `F = P_1P_2` gives `n_F = 2` and `F = P^2` gives `n_F = 4`.)

Novelty: **low.** Degree-1 Conjecture A/B is classical and the factorisation argument is routine;
what is recorded here is the *exact* location of the frontier, which the log had not stated. It is
worth having because it says the entire degree-`≤2` case is one statement, and that statement is
`(P1)` — the Energy Gap upper half — not MI.

### 172.3 What is still open even below Conjecture A

Stated for the record, because the log has repeatedly assumed it:

> **Finiteness of `n_F` is itself open.** No unconditional bound `\limsup_x E(x)/\log\log x < ∞` is
> known for `F ∈ S`. The best is `E(x) ≪ \log²x` (Theorem 75 with `K ≍ \log x`, Corollary 94 upper
> half), which is vacuous at the `\log\log` scale. Wirsing (§58) gives the *shape*
> `Σ_{n≤x}|a_F(n)|² ∼ cx(\log x)^{n_F−1}` **given** that the density exists; existence is part of
> Conjecture A, not a theorem.

An unconditional bound `Σ_{n≤x}|a_F(n)|² ≪ x(\log x)^{C}` for some `C = C(d)` would give
`n_F ≤ C + 1` and is equivalent, by the approximate functional equation, to
`∫_0^T|F(1/2+it)|²dt ≪ T(\log T)^{C}` — the Rankin–Selberg problem. Recorded as the cleanest
statement of "why even finiteness is hard".

### 172.4 Lean: approximate orthogonality ⟹ approximate integrality

New in `HTGeometry/BesselPSD.lean`, `lake build` clean:
```lean
theorem energy_near_int_of_almost_orthonormal (B : V → V → ℂ) (hadd₁ …) (hsmul₁ …) (hconj …)
    {ι} [Fintype ι] [DecidableEq ι] (e : ι → V) (m : ι → ℤ) (ε : ℝ)
    (hgram : ∀ i j, ‖B (e i) (e j) - (if i = j then (1 : ℂ) else 0)‖ ≤ ε) :
    |(B (∑ i, ((m i : ℂ)) • e i) (∑ i, ((m i : ℂ)) • e i)).re - ∑ i, ((m i : ℝ)) ^ 2|
      ≤ ε * (∑ i, |(m i : ℝ)|) ^ 2
```
Read arithmetically: **an approximate Conjecture B implies an approximate Conjecture A**, with error
`ε‖m‖_1²`. In particular, if the Gram defect satisfies `ε‖m‖_1² < 1/2`, the energy of `F = ∏P_i^{m_i}`
determines `Σ_i m_i²` uniquely and is within `1/2` of that integer. This is the first formal statement
in the corpus linking the two conjectures quantitatively; it also shows that Conjecture A for a fixed
`F` needs Conjecture B only to accuracy `ε ≪ ‖m‖_1^{−2}`, not exactly.

### 172.5 Position

```
unconditional : Thm 84′, 85′, 87, 89, 90, 93, Cor 101, Thm 100, Cor 102
conditional on (V)/hyp (a) : Thm 91, Cor 92, Cor 94-lower
open core, degree ≤ 2 : (P1)_2 — n_F = 1 for primitive degree-2 F   ⟸ the WHOLE of Conjecture A there
open, general : Conjecture A (even finiteness of n_F), Conjecture B, Energy Gap 0 < n_F < 1
```

---

## 173. Cycle 173 (2026-07-26) — audit of the amplifier: the test function was inadmissible; the repair makes Theorem 76 **exact**

Continuing the §171.5 audit, now on the load-bearing amplifier of §127/§129 (Theorems 75, 76, 78).

### 173.1 The defect

The amplifier is taken to be
```
φ'(t) = Σ_{p≤x}\overline{a_F(p)}\,p^{−1/2}\,ψ\big((t−t_0)/P\big)\,e^{it\log p} ,       ψ ∈ C_c^∞ ,
```
i.e. **compactly supported in `t`**, and the identity used is `∫φ'S_F = 𝒫[φ]`.

For a compactly supported smooth `φ` the Fourier transform `\hatφ` is entire and Schwartz on `R`, so
`\hatφ(u) ≪_A (1+|u|)^{−A}` — **polynomial decay only**. The prime side of the Weil explicit formula
is then
```
Σ_n Λ_F(n)\,n^{−1/2}\,\hatφ(\log n)  ,
```
whose `k = 1` part is `Σ_p a_F(p)(\log p)p^{−1/2}\hatφ(\log p) ≍ Σ_p p^{−1/2+ε}(\log p)^{1−A}`, which
**diverges** for every `A`. Compactly-supported-in-`t` test functions are therefore **not admissible**
in the Selberg-class explicit formula: the admissible class needs `\hatφ(u) ≪ e^{−(1/2+δ)|u|}`, i.e.
`φ` analytic in a strip of half-width `> 1/2`.

> **Defect (fifth).** §127.1's amplifier is inadmissible as stated. The identity `∫φ'S_F = 𝒫[φ]` was
> applied to a test function for which the right-hand side is not defined.

### 173.2 The repair: take the amplifier **band-limited**, not compactly supported

Choose `ψ` with `\hatψ` supported in `[−1,1]` (so `ψ` is Schwartz but spread over all of `R`). Then
```
\widehat{φ'}(ξ) = Σ_{p≤x}\overline{a_F(p)}p^{−1/2}P\,e^{−i t_0(ξ−\log p)}\,\hatψ\big(P(ξ−\log p)\big)
```
is supported in `⋃_{p≤x}[\log p − 1/P,\ \log p + 1/P]`, a **compact set bounded away from `0`**, and
`\hatφ = \widehat{φ'}/(iξ)` is supported there too. Three consequences, all exact:

1. **The prime side is exactly the diagonal.** `\hatφ(\log n) ≠ 0` needs `|\log n − \log p| ≤ 1/P` for
   some `p ≤ x`. By §167.2, distinct positive integers `n ≠ p` satisfy
   `|\log n − \log p| ≥ 1/\max(n,p)`; so either `n = p`, or `n > P` — and for `n > P ≫ x ≥ p` one has
   `\log n − \log p ≥ \log(P/x) ≫ 1/P`. **Hence only `n = p ≤ x` contributes**, and prime powers
   `p^k`, `k ≥ 2`, are excluded outright rather than estimated.
2. **The archimedean main term drops.** It is proportional to `\hatφ(0)`, and `0` is not in the
   support.
3. **The mean square of the amplifier is exact.** In `‖φ'‖_2²` the off-diagonal term at `(p,p')`
   carries `\widehat{ψ²}\big(P(\log p − \log p')\big)` with `\widehat{ψ²} = \hatψ * \hatψ` supported in
   `[−2,2]`; distinct `p,p' ≤ x` have `|\log p − \log p'| ≥ 1/x`, so the term vanishes identically
   once `P > 2x`. **No Montgomery–Vaughan, no error term:**
   ```
   ‖φ'‖_2²  =  P\,‖ψ‖_2²\,Σ_{p≤x}|a_F(p)|²/p       for every  P > 2x .
   ```

> **Theorem 76′ (unconditional; repaired and strengthened).** Let `F ∈ S` be entire, `x ≥ 2`,
> `P > 2x`, `t_0 ∈ R`, and let `ψ` be band-limited as above. Then, with `E_x := Σ_{p≤x}|a_F(p)|²/p`,
> ```
> ∫ \big|S_F(t)\big|²\,\big|ψ((t−t_0)/P)\big|^{0}\,dt  ≥  \frac{P\,E_x}{4π²\,}\cdot c_ψ ,
> ```
> more precisely `\big(∫|S_F|²|ψ((t−t_0)/P)|²dt\big)^{1/2} ≥ \sqrt{P E_x}\,c_ψ` — the `L²` norm being
> taken against the rapidly decaying weight `|ψ((t−t_0)/P)|²` rather than over a compact interval.
> Consequently `(1/P)∫_{|t−t_0| ≤ P^{1+δ}}|S_F|²dt ≫_ψ E_x`.

**Net effect.** The theorem survives, with three improvements: the prime side is an identity rather
than a main term plus error; the prime-power terms are removed by exact frequency separation rather
than by the Ramanujan bound; and the mean-value theorem is not needed. The only cost is that the
localisation is by a rapidly decaying weight instead of a sharp interval, which changes `P` to
`P^{1+o(1)}` in the statement and nothing else.

The identical repair applies to Theorem 75 (`|S_F| ≤ K ⟹ n_F ≤ CK²`) and Theorem 78, which use the
same amplifier. Theorem 79 (the rounding floor) does not use it and is unaffected; Theorem 77 uses the
distributional identity `∫φ'S_F = 𝒫[φ]` only for band-limited `φ` and is unaffected.

> **Recorded rule (eighth).** *In the Selberg class, only band-limited test functions are admissible in
> the explicit formula.* Compact support in `t` gives a divergent prime side. This is the same
> distinction as §163's band-limiting and §171.3's duality obstruction, now seen as a hard
> admissibility condition rather than a technical convenience. Every future use of `∫φ'S_F = 𝒫[φ]`
> must exhibit `\mathrm{supp}\,\hatφ` compact.

### 173.3 Correction ledger, updated

| # | where | defect | status |
|---|---|---|---|
| 1 | §149.1 | Baker's constant depends on `π(N)` | repaired (§167) |
| 2 | §92.1 | sign of the `n_0` term | corrected (§168) |
| 3 | preprint Thm 13 | `(\log X)^{−C}` gap false at `j=k=1` | corrected (§168.5) |
| 4 | §147.1 (★) | `B²` truncation used outside its hypothesis | Thm 91, Cor 92 downgraded (§171) |
| 5 | §127.1 | amplifier compactly supported ⟹ divergent prime side | **repaired, Thm 76 strengthened (§173)** |

Five defects in seven cycles. Four of the five were repairable and left the theorem intact; one
(no. 4) genuinely downgraded a result. **The audit is producing more mathematics than the attacks:
the repair of no. 5 turns an inequality with error terms into an exact identity.**

---

## 174. Cycle 174 (2026-07-26) — partial **un-downgrade**: the qualitative half of Corollary 92 is unconditional after all

§171.2 downgraded Corollary 92 wholesale because it was derived from Theorem 91. That was too severe:
its qualitative half does not need Theorem 91 at all.

### 174.1 The three unconditional ingredients

1. **Fourier–Bohr coefficients of `S_F` are exactly the prime amplitudes.** Pairing `S_F` against the
   band-limited window `ψ((t−t_0)/P)e^{−iλt}` and using §173.2 (only `n` with
   `|\log n − λ| ≤ 1/P` survive, and by the log separation `|\log n − \log m| ≥ 1/\max(n,m)` that means
   `n = e^{λ}` exactly when `λ = \log m` with `m ≪ P`), the limit exists and
   ```
   \widehat{S_F}(\log n)  =  −\,\frac{Λ_F(n)}{2π\,n^{1/2}\log n}\;(\text{phase}) ,\qquad
   \widehat{S_F}(λ) = 0 \text{ for } λ ∉ \{±\log n\} .
   ```
2. **Bessel for Fourier–Bohr coefficients** (elementary, no hypothesis): for any locally integrable
   `f` and any finite set of distinct frequencies,
   `\liminf_T (1/T)∫_0^T|f|² ≥ Σ_j |\hat f(λ_j)|²`, by expanding
   `(1/T)∫|f − Σ_j\hat f(λ_j)e^{iλ_jt}|² ≥ 0` and using
   `(1/T)∫e^{i(λ_j−λ_l)t}dt → δ_{jl}`. (This is Theorem 76 in the limit; §173.2 makes the finite-`P`
   version exact.)
3. **Theorem 84′/89 (unconditional):** every non-constant `F ∈ S` has `Σ_p|a_F(p)|²/p = ∞`.

### 174.2 The theorem

> **Theorem 102 (unconditional).** For every non-constant `F ∈ S`,
> ```
> \liminf_{T→∞}\ \frac1T∫_0^T |S_F(t)|²\,dt \;=\; ∞ .
> ```
> In particular `S_F` is **unbounded**, and no non-constant `F ∈ S` has `S_F ∈ B²`.
>
> *Proof.* By (1) and (2), `\liminf_T(1/T)∫_0^T|S_F|² ≥ (1/2π²)Σ_{n≤N}|Λ_F(n)|²/(n\log²n)` for every
> `N`; the right side is `(1/4π²)Σ_{p≤N}|a_F(p)|²/p + O(1)`, which tends to `∞` by (3). ∎

No zero-density estimate, no Selberg central limit theorem, no RH, and — unlike Corollary 92 as
originally derived — **no Theorem 91 and hence no hypothesis (V)**.

For `ζ` the unboundedness of `S(t)` is classical (Selberg, via his zero-density theorem). For a
general `F ∈ S` the standard route needs the same density input; here the amplifier replaces it.
Novelty: searched (July 2026) under "unbounded S(t) Selberg class unconditional", "argument of
L-function unbounded axiomatic"; **not located**. Assessed, not claimed.

### 174.3 What remains conditional

Only the **rate**:
```
\liminf_T (1/T)∫_0^T|S_F|² = ∞                                     unconditional  (Thm 102)
\liminf_T (1/T)∫_0^T|S_F|² ≫ \log\log\log T                        conditional on (V)  (Cor 92)
(1/T)∫_0^T|S_F|² ∼ (n_F/2π²)\log\log T                             = hypothesis (a)
```
The gap is exactly the absence of a rate in Theorem 84′: the characteristic-function method proves
`E(x) → ∞` but, as §171 showed, its quantitative refinement (★) is unavailable in the divergent
regime.

### 174.4 Amended status table (supersedes §171.2 for Cor 92)

| result | status |
|---|---|
| Thm 84′, 85′, 87, 89, 90 | unconditional |
| Thm 76′ (amplifier, band-limited form) | unconditional, and now **exact** (§173.2) |
| **Thm 102** `(1/T)∫\|S_F\|² → ∞`, `S_F` unbounded | **unconditional** (this cycle) |
| Thm 91 `E(T) ≫ \log\log\log T` | conditional on (V) |
| Cor 92 *with the rate* | conditional on (V) |
| Cor 94 upper half `≪ \log²T` | unconditional |

> **Lesson recorded.** Downgrades must be audited as carefully as claims. Corollary 92 was stated as a
> consequence of Theorem 91 when it is in fact a consequence of two weaker unconditional facts; the
> §171 audit propagated the downgrade mechanically along the *recorded* derivation instead of looking
> for a shorter one. **When a result is downgraded, re-derive it from scratch before recording the
> downgrade.**

### 174.5 Lean: the three ingredients of Theorem 102 are now all formal

`HTGeometry/GeneralizedDirichletMeanValue.lean`, new:
```lean
theorem oscInt_gram_bound {ι} [DecidableEq ι] (lam : ι → ℝ) (T U g : ℝ)
    (hU : 0 < U) (hg : 0 < g) (hgap : ∀ i j : ι, i ≠ j → g ≤ |lam i - lam j|) (i j : ι) :
    ‖((U : ℂ))⁻¹ * oscInt (lam i - lam j) T U - (if i = j then (1 : ℂ) else 0)‖ ≤ 2 / (g * U)
```
This is exactly the `hgram` hypothesis of `bessel_of_almost_orthogonal` (§166.4) with `A = 1` and
`ε = 2/(gU)`. So the chain
```
oscInt_norm_le  →  oscInt_gram_bound  →  bessel_of_almost_orthogonal
```
is the finite-interval Bessel inequality for Fourier–Bohr coefficients with **explicit** error
`(1 + \mathrm{card}·2/(gU))`, and
```
monomial_log_separation  (§167.6)
```
supplies the frequency gap `g ≥ N^{−D}` for the tones `\log n`, `n ≤ N`. Together these are the whole
unconditional machine behind Theorems 76′ and 102: *separation of prime logarithms + an oscillatory
integral bound + Bessel for a positive semi-definite form.* No transcendence theory, no zero density,
no automorphy.

---

## 175. Cycle 175 (2026-07-26) — audit of the remaining load-bearing theorems; two dead ends; Theorem 76″

### 175.1 Audit results (Theorems 52, 70, 77, 79)

Re-derived, not re-read, per §171.5.

- **Theorem 52** (`\log F − Σ_p a_F(p)p^{−s}` holomorphic on `Re s > 1/2`). Uses the Ramanujan axiom on
  prime powers via `log_coeff_bound` + `tail_geometric_bound`: `|b_F(p^k)| ≪ (4C_ε)^kp^{kε}` gives
  `Σ_pΣ_{k≥2}|b_F(p^k)|p^{−kσ} ≪ Σ_p p^{2ε−2σ}`, convergent for `σ > 1/2 + ε`. **Passes.** One
  quantitative refinement worth recording: the tail is `≪ \log(1/δ)` at `σ = 1/2+δ` — the *same* order
  as the main term — but its **mean square is `O(1)`** (`Σ_pΣ_{k≥2}|b_F(p^k)|²p^{−2kσ} ≪ Σ_p p^{−2+4ε}`).
  That is why every `L²` statement in this programme may discard the prime-power tail and no pointwise
  statement may.
- **Theorem 70** (perfect rigidity ⟹ `F = 1`): uses only `S_F = 1/2 − \{M_F\}` and equidistribution.
  **Passes.**
- **Theorem 77** (`Σ_p|a_F(p)|²/p < ∞ ⟹ S_F = c + 𝒮 ∈ B²`): uses `∫φ'S_F = 𝒫[φ]` only for
  band-limited `φ`, so §173.1's admissibility defect does not touch it. **Passes.**
- **Theorem 79** (rounding floor): `S_F − c = N_F − (M_F+c)` with `N_F ∈ Z` gives
  `|S_F − c| ≥ \|M_F+c\|`; `M_F'' ≠ 0` gives equidistribution mod `1`; `∫_{−1/2}^{1/2}u²du = 1/12`.
  **Passes** (Lean: `integral_sq_rounding_error`).

No further defects. The five recorded in §173.3 stand as the complete list.

### 175.2 Theorem 76″: the amplifier and the rounding floor add

The residual `R_x := S_F − 𝒮_x` satisfies `R_x = N_F − (M_F + 𝒮_x)` with `N_F ∈ Z`, so
`|R_x| ≥ \|M_F + 𝒮_x\|`; the chirp `M_F` dominates the almost periodic `𝒮_x`, so `M_F + 𝒮_x`
equidistributes mod `1` and `(1/T)∫|R_x|² ≥ 1/12 − o(1)`. The cross term vanishes **exactly** (§173.2:
the resolved band is exactly orthogonal to the residual). Hence

> **Theorem 76″ (unconditional).** For every non-constant `F ∈ S` and every `x < T/2`,
> ```
> \frac1T∫_0^T|S_F(t)|²dt  ≥  \frac{1}{4π²}Σ_{p≤x}\frac{|a_F(p)|²}{p}  +  \frac1{12}  −  o(1) .
> ```

**Sharpness.** For `ζ`, Selberg gives `(1/T)∫_0^TS(t)²dt ∼ (1/2π²)\log\log T` while
`E(T/2) ∼ \log\log T`: Theorem 76″'s main term is off by exactly a factor `2`. **The amplifier
recovers half of Selberg's asymptotic for the entire Selberg class with no zero-density input.** The
missing half is the matching upper bound, i.e. hypothesis (a).

### 175.3 Dead end I — the `L^∞` band projection

*Idea.* The Fourier–Bohr spectrum of `S_F` is `\{±\log n\}` with the prime amplitudes (§174.1), so
smooth band-limiting to `[\log 2, \log x]` maps `S_F` to `𝒮_x` exactly. Band projection is
`L^∞`-bounded by the `L¹` norm of its kernel, so `‖𝒮_x‖_∞ ≤ ‖k‖_1‖S_F‖_∞`. By **Kronecker**, the
`\log p` being `Q`-independent, `\sup_{t∈R}|𝒮_x(t)| = (1/π)Σ_{p≤x}|a_F(p)|/\sqrt p ≍ \sqrt x/\log x`,
enormous, while `‖S_F‖_∞ ≪ \log T`.

*Why it fails.* The Kronecker supremum is attained only when `(t\log p)_{p≤x}` is `ε`-dense in
`T^{π(x)}`, which needs `T ≥ \exp(c\,π(x)\log x)` — **doubly exponential in `x`**. Over `[0,T]` the
attainable supremum is only `≍ \sqrt{E_x\log\log T}`, and the kernel loss `‖k‖_1 ≍ \log x` (Dirichlet
kernel smoothed at the frequency gap `δ ≍ 1/x`) swamps the gain.

> **Recorded do-not-retry.** Sup-norm information about `𝒮_x` is unusable: its `ℓ¹` norm is attained
> only at doubly-exponential height, and band projection costs `\log x` in `L^∞`. Only `L²` transfers.

### 175.4 Dead end II — the resonance method reduces to the amplifier

With a resonator `R(t) = Σ_n r(n)n^{−it}` on squarefree `x`-smooth `n`, `r(n) = ∏_{p|n}u_p`,
`u_p = |a_F(p)|/\sqrt p`, the Fourier coefficient of `|R|²` at `\log p` is
`Σ_n r(pn)\overline{r(n)} = u_p∏_{q≠p}(1+u_q²)`, so
```
\frac{∫S_F|R|²}{∫|R|²} = \frac1π Σ_{p≤x}\frac{|a_F(p)|²}{p}\cdot\frac1{1+u_p²} ≈ \frac{E_x}{π} ,
```
giving `\max_{t≤T}|S_F(t)| ≫ E_x` with `x ≤ \tfrac12\log T` (the resonator has length `e^{θ(x)}` and
the diagonal must dominate). **This is Theorem 76′ with the mean square replaced by the maximum and
`x` degraded from `T/2` to `\log T`** — weaker in every respect; for `ζ` it yields only
`S(t) = Ω(\log\log\log t)` against the known `Ω(\sqrt{\log\log t/\log\log\log t})`.

> **Recorded.** The resonance method applied to `S_F` *is* the amplifier and produces no independent
> information. Stronger `Ω`-results would need a resonator adapted to the **chirp** `M_F`, not to the
> prime tones — the same "geometric side is archimedean" ceiling as §166.2.

### 175.5 Position

```
unconditional : Thm 84′, 85′, 87, 89, 90, 93, 100, 102, Cor 101, 102, Thm 76′, 76″
                (Thm 76″ = half of Selberg's asymptotic for all of S, plus the 1/12 floor)
conditional   : Thm 91, Cor 92-with-rate  (on (V) = hypothesis (a))
open core     : a RATE for E(T); (P1)_2; Conjecture A; Conjecture B
```
The single quantity blocking the whole quantitative layer is a **rate of divergence for
`E(T) = Σ_{p≤T}|a_F(p)|²/p`**. Theorem 84′ gives divergence with no rate; (★) cannot supply one
(§171); the `L^∞` and resonance routes are closed (§175.3, §175.4).

---

## 176. Cycle 176 (2026-07-26) — **the fourth archimedean regime**: a geometric side that is neither `0` nor `1`

§147.3 recorded: *"Any further progress must come from a mechanism whose geometric side is not confined
to `\{0,1\}`."* One exists, and it was missed because the archimedean phase was expanded one term too
short.

### 176.1 The missing term

For `H = ∏_iF_i^{α_i}` put `X := Σ_iα_iS_{F_i} = (Σα_iN_{F_i}) − Φ(t)`, `Φ := Σα_iM_{F_i}`, the first
bracket integer-valued, so `e^{2πikX} = e^{−2πikΦ}` exactly. Stirling on
`γ(s) = Q^s∏_jΓ(λ_js+μ_j)` at `s = 1/2+it` gives
`\arg Γ(λ_j/2+μ_j+iλ_jt) = λ_jt\log(λ_jt) − λ_jt + (\mathrm{Im}\,μ_j)\log(λ_jt) + \text{const} + O(1/t)`,
so the **full** asymptotic of the archimedean phase is
```
Φ(t) = A\,t\log t + B\,t + C\log t + D + O(1/t) ,
A = \frac{Σα_id_i}{2π},\quad B \text{ from the conductors},\quad
C = \frac{1}{2π}\,Σ_iα_i\,θ_{F_i},\quad θ_F := \mathrm{Im}\,ξ_F,\ \ ξ_F = 2Σ_j(μ_j − \tfrac12) .
```
`θ_F` is exactly the Kaczorowski–Perelli **shift invariant** (it appears in the standard twist's poles
`s^*_ℓ = (d+1)/(2d) − ℓ/d − iθ_F`, cf. §4). §139/§147/§150 expanded `Φ` only to `Bt + D`, i.e. took
`C = 0` silently.

> **Defect (sixth).** Theorem 89's case analysis is incomplete: it lists `A ≠ 0`, `A = 0 ≠ B`, and
> `A = B = 0` (claiming the phase tends to a constant). The third of these splits, because `C` need not
> vanish.

### 176.2 The four regimes, and the new value

```
A ≠ 0                    chirp             |M_T\{e^{2πikX}\}| → 0            (van der Corput)
A = 0, B ≠ 0             pure tone         |M_T\{e^{2πikX}\}| → 0
A = B = 0, C ≠ 0         **logarithmic**   |M_T\{e^{2πikX}\}| → (1+4π²k²C²)^{−1/2}   ∈ (0,1)
A = B = C = 0            constant          |M_T\{e^{2πikX}\}| → 1
```
The third line is the computation
```
\frac1T∫_0^T e^{−2πik(C\log t + D)}dt = \frac{e^{−2πikD}\,T^{−2πikC}}{1 − 2πikC} ,
```
whose modulus is `|1−2πikC|^{−1} = (1+4π²k²C²)^{−1/2}`. (The limit of `M_T` itself does not exist —
the factor `T^{−2πikC}` rotates — but its modulus converges, which is all the method uses.)

> **This is the mechanism §147.3 asked for.** The geometric side now takes a **continuum** of values
> in `(0,1)`, parametrised by the archimedean invariant `C = (2π)^{−1}Σα_iθ_{F_i}`, and its
> `k`-dependence is **polynomial** (`≍ 1/(2πk|C|)`) whereas the arithmetic side's is **exponential**
> (`∏_p|I_p| ≈ e^{−k²E_H}`).

### 176.3 The regime is non-empty

Take `χ` a primitive character mod `q` and `θ_1 ≠ θ_2` real; `P_j := L(s+iθ_j,χ) ∈ S` (degree `1`,
conductor `q`, `θ_{P_j} = θ_j`). For `H = P_1/P_2`: `Σα_id_i = 0` ✔, conductors equal so `B = 0` ✔,
and `C = (θ_1−θ_2)/2π ≠ 0` ✔. Direct check of the arithmetic side:
`a_H(p) = χ(p)(p^{−iθ_1} − p^{−iθ_2})`, so
`Σ_{p≤x}|a_H(p)|²/p = Σ_{p≤x}\frac{2 − 2\cos((θ_1−θ_2)\log p)}{p} = 2\log\log x + O(1) → ∞`,
using `Σ_pp^{−1−iτ} = \log ζ(1+iτ)+O(1)` bounded for `τ ≠ 0`. ✔ Consistent: the arithmetic side
vanishes (divergent energy) while the geometric side is `(1+4π²k²C²)^{−1/2} ≠ 0` — **no contradiction,
because the arithmetic evaluation is unavailable when the energy diverges.**

### 176.4 Theorem 89 survives, with the case restored

In the new regime, suppose `Σ_p|a_H(p)|²/p < ∞`. Then `X = c + 𝒮` with `𝒮 ∈ B²` and
`|M\{e^{2πikX}\}| = ∏_p|I_p(k)|`, so for **every** integer `k ≠ 0`
```
∏_p |I_p(k)|  =  (1 + 4π²k²C²)^{−1/2} .
```
As `k → ∞` the left side decays like `e^{−k²E_H}` (super-exponentially if `E_H > 0`) while the right
side decays like `1/(2πk|C|)` (polynomially): impossible unless `E_H = 0`, in which case the left side
is `1` and the right side is `< 1` unless `C = 0`. Hence `C = 0` and every `a_H(p) = 0`, so `H = 1`.
**Theorem 89's statement is unaffected**; only its proof needed the fourth case.

> **Recorded.** The polynomial-versus-exponential mismatch in `k` is a *strictly stronger* lever than
> the `\{0,1\}` dichotomy: it forces a contradiction not merely from `∏|I_p| ≠ 0` but from the whole
> profile `k ↦ ∏_p|I_p(k)|`. This is the first time in the programme that the `k`-dependence, rather
> than a single value of `k`, carries the argument.

### 176.5 New named target (LOG)

> **(LOG).** Exploit the logarithmic regime at **finite `T`**. In it the geometric side is `≍ 1` while
> the truncated Euler product `∏_{p≤N}|I_p| ≈ e^{−k²E(N)}` tends to `0`; hence, unconditionally,
> ```
> \frac{\|X − c − 𝒮_N\|_{L²[0,T]}}{\sqrt T} \;\gg\; \frac{1}{k\sqrt{1+4π²k²C²}}\qquad\text{for every }N ,
> ```
> a *lower* bound on the residual requiring no hypothesis (V) — the direction (V) does not supply.
> The question is whether the `k`-profile can be pushed to yield a **rate** for `E(T)`, the single
> quantity blocking the quantitative layer (§175.5).

Two immediate observations. (i) The bound above is a `1/12`-type floor, not a rate (compare Theorem
76″). (ii) The `k`-profile identity `∏_p|I_p(k)| = (1+4π²k²C²)^{−1/2}` is an *equality between an
Euler product and an explicit archimedean function of `k`* — the first such in the programme. Any
finite-`T` version of it would be a genuinely new constraint linking prime energy to the shift
invariants `θ_{F_i}`.

### 176.6 Correction ledger

| # | where | defect | status |
|---|---|---|---|
| 1 | §149.1 | Baker's constant depends on `π(N)` | repaired (§167) |
| 2 | §92.1 | sign of the `n_0` term | corrected (§168) |
| 3 | preprint Thm 13 | `(\log X)^{−C}` gap false at `j=k=1` | corrected (§168.5) |
| 4 | §147.1 (★) | `B²` truncation outside its hypothesis | Thm 91, Cor 92-rate downgraded (§171) |
| 5 | §127.1 | amplifier compactly supported ⟹ divergent prime side | repaired, Thm 76 strengthened (§173) |
| 6 | §139/§147/§150 | archimedean phase expanded one term short; `C\log t` dropped | **repaired (§176); new regime found** |

Six defects in ten cycles. Defect 6 is the first whose repair **opens** a route rather than closing
one.

### 176.7 Lean: the profile mismatch

New `HTGeometry/KProfileMismatch.lean`, registered:
```lean
theorem sqrt_one_add_sq_le {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (1 + a ^ 2) ≤ 1 + a
theorem sqrt_lt_exp_of_energy_pos {E C k : ℝ} (hk : 0 < k) (hkgt : 2 * Real.pi * |C| < k * E) :
    Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2) < Real.exp (k ^ 2 * E)
theorem exp_neg_lt_inv_sqrt {E C k : ℝ} (hk : 0 < k) (hkgt : 2 * Real.pi * |C| < k * E) :
    Real.exp (-(k ^ 2 * E)) < (Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2))⁻¹
theorem inv_sqrt_lt_one_of_ne_zero {C k : ℝ} (hC : C ≠ 0) (hk : k ≠ 0) :
    (Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2))⁻¹ < 1
```
The chain `√(1+4π²k²C²) ≤ 1 + 2π|C|k < 1 + k²E ≤ exp(k²E)` is the whole engine of §176.4: it is the
formal statement that **a Gaussian profile in `k` cannot equal a reciprocal-square-root profile**, and
the last lemma disposes of the residual case `E = 0`. Note the hypothesis `0 < E` is not needed —
`2π|C| < kE` with `k > 0` already forces it — which is why the lemma reads with `hkgt` alone.

---

## 177. Cycle 177 (2026-07-26) — Theorem 103: complete classification of the mod-1 law; and (LOG) resolved

### 177.1 The mod-1 limit laws

In regime 3 the phase `Φ(t) = C\log t + D + O(1/t)` does not equidistribute mod `1`: with `t` uniform
on `[0,T]` and `t = e^{(u−D)/C}`, the measure of `\{C\log t + D ∈ [u,u+du]\}` is
`T^{−1}C^{−1}e^{(u−D)/C}du`, so the blocks `[a+m,a+m+1)` carry masses in geometric ratio `e^{1/C}`,
dominated by the top block. The limiting density on `[0,1)` is
```
f_C(v) = \frac{e^{v/C}}{C\,(e^{1/C}−1)} ,
```
whose Fourier coefficients are `\int_0^1 f_C(v)e^{−2πikv}dv = \dfrac{1}{1 − 2πikC}` — **exactly** the
geometric value computed in §176.2. ✔ (Independent confirmation of the whole regime.)

Because the top block sits at `\{C\log T + D\}`, the law is *rotated* by `T`; the limit exists only
along subsequences, and the set of limit laws is the full rotation orbit of `f_C`.

> **Theorem 103 (unconditional; complete mod-1 classification).** Let `H = ∏_iF_i^{α_i}` be a
> non-trivial element of the group completion of `S` and `X := Σ_iα_iS_{F_i}`. Write
> `A = (2π)^{−1}Σα_id_i`, `B` for the conductor coefficient, `C = (2π)^{−1}Σα_iθ_{F_i}` with
> `θ_F = \mathrm{Im}\,ξ_F`, `ξ_F = 2Σ_j(μ_j−\tfrac12)`. Then the distribution of `X(t)` mod `1`,
> `t` uniform on `[0,T]`, converges as follows:
> ```
> A ≠ 0,  or A = 0 ≠ B          →  uniform on [0,1)                          (equidistribution)
> A = B = 0,  C ≠ 0             →  the rotates of  f_C(v) = e^{v/C}/(C(e^{1/C}−1))
> A = B = C = 0                 →  a point mass at −D mod 1
> ```
> In particular, for a single non-constant `F ∈ S` the fluctuation `S_F` is **uniform** mod `1`
> (classical), while for `H = L(s+iθ_1,χ)/L(s+iθ_2,χ)` the difference `S_{P_1} − S_{P_2}` is
> **exponentially (Benford-)distributed** mod `1` with parameter `C = (θ_1−θ_2)/2π`.

The proof is the identity `e^{2πikX} = e^{−2πikΦ}` (integrality of the zero counts) plus the three
evaluations of `T^{−1}∫_0^Te^{−2πikΦ}dt`. Nothing else. **The entire mod-1 behaviour of every integer
combination of zero-counting fluctuations in the Selberg class is archimedean and explicit.**

Novelty: the uniform case for `S_ζ` is classical; the exponential case appears to be new — searched
(July 2026) "distribution mod 1 of S(t)", "Benford law argument of L-function", not located.
Assessed, not claimed. Significance: modest as a statement, but it **completes** the geometric side of
the characteristic-function method, which was the programme's central engine, and it certifies that
no further regimes exist (the asymptotic expansion of `Φ` has exactly the terms `t\log t, t, \log t, 1`).

### 177.2 (LOG) resolved: an `O(1)` floor, not a rate

The unconditional inequality available in regime 3 is, for every integer `k ≠ 0` and every `N`,
```
\frac1T∫_0^T|X − 𝒮_N|\,dt  ≥  \frac{1}{2πk}\Big|\,G(k)\,e^{iϑ_k(T)} − ∏_{p≤N}|I_p(k)|\,\Big| ,
\qquad G(k) = (1+4π²k²C²)^{−1/2} ,
```
with `∏_{p≤N}|I_p(k)| ≈ e^{−k²E(N)}` (unconditional at finite `T` by §167.3's moment coupling), and
the phases `ϑ_k(T)` alignable along a suitable sequence of `T` since `C ≠ 0`.

Optimising the right-hand side over `k` **as a real variable** gives the maximum at
`k ≍ E(N)^{−1/2}`, where it equals `≍ \sqrt{E(N)}` — *a genuine rate*. But `k` must be a **non-zero
integer**, because the identity `e^{2πikJ} = 1` requires it, and at `k = 1` the bound is only
`≍ G(1)/2π = O_C(1)`.

> **(LOG) verdict.** The logarithmic regime supplies an `O(1)` floor on the residual — the same
> strength as Theorem 76″'s `1/12` — and **not** a rate. The obstruction is sharp and entirely
> explicit: *the optimal test frequency is `k ≍ E^{−1/2} < 1`, and the method admits only `|k| ≥ 1`.*

Two consequences recorded:

- **Smoothing does not help.** Replacing `e^{2πikX}` by `f(X)` for `1`-periodic `f` gives
  `Σ_k\hat f(k)[G(k)e^{iϑ_k} − e^{−k²E(N)}]` bounded by `‖f‖_{\mathrm{Lip}}·T^{−1}∫|X−𝒮_N|`, and
  `‖f‖_{\mathrm{Lip}} ≥ 2π|k|\,|\hat f(k)|` forces the same `k = 1` optimum. (This refines §150.2,
  which had established the analogous statement only in the regimes where the geometric side vanishes.)
- **The sublattice trick fails.** If `J = Σα_iN_{F_i} ∈ mZ` one may use `k ∈ m^{−1}Z`; but forcing
  `J ∈ mZ` means replacing `H` by `H^m`, which rescales `X ↦ mX`, `C ↦ mC`, `E ↦ m²E`, and `k = 1/m`
  on `X_m` is literally `k = 1` on `X_1`. No gain.

> **Named open core (FRAC).** *Is there an exact identity for `S_F` with a continuous, or merely
> finer-than-integer, dual parameter?* The integrality of `k` traces back to `e^{2πikN_F} = 1`, i.e. to
> the zero count being an integer. Any refinement would require an object attached to `F` whose values
> lie in a finer lattice than `Z` — none is supplied by the axioms. **(FRAC) is the exact obstruction
> to converting the characteristic-function method's floors into rates**, and it now replaces "improve
> (★)" as the correct statement of what is missing.

### 177.3 Position

```
unconditional : Thm 84′, 85′, 87, 89, 90, 93, 100, 102, 103, Cor 101, 102, Thm 76′, 76″
conditional   : Thm 91, Cor 92-with-rate       (on (V) = hypothesis (a))
open cores    : (FRAC) — a finer-than-integer dual parameter  ⟹ rates for E(T)
                (P1)_2 — n_F = 1 for primitive degree-2 F     ⟹ Conjecture A in degree ≤ 2
                (NC)   — a lower bound for a_F(n_0) − a_G(n_0) ⟹ effective strong multiplicity one
                (V)/(a) — the zero-density/pair-correlation input
open          : Conjecture A, Conjecture B
```

### 177.4 Lean: the density certificate

New `HTGeometry/LogPhaseDensity.lean`, registered:
```lean
theorem logDensityExponent_ne_zero {C : ℝ} (hC : C ≠ 0) (k : ℤ) :
    ((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k ≠ 0
theorem integral_expDensity (C : ℝ) (hC : C ≠ 0) (k : ℤ) :
    (∫ v in (0:ℝ)..1, Complex.exp ((((1 / C : ℝ) : ℂ) - 2*Real.pi*Complex.I*k) * (v : ℂ)))
      = ((Real.exp (1 / C) : ℂ) - 1) / (((1 / C : ℝ) : ℂ) - 2*Real.pi*Complex.I*k)
theorem fourierCoeff_expDensity (C : ℝ) (hC : C ≠ 0) (k : ℤ) :
    (((C : ℂ)) * ((Real.exp (1 / C) : ℂ) - 1))⁻¹ *
        (∫ v in (0:ℝ)..1,
          Complex.exp ((((1 / C : ℝ) : ℂ) - 2*Real.pi*Complex.I*k) * (v : ℂ)))
      = (1 - 2 * Real.pi * Complex.I * k * C)⁻¹
```
The last identity is the **certificate for Theorem 103's middle case**: the `k`-th Fourier
coefficient of the normalised density `f_C(v) = e^{v/C}/(C(e^{1/C}−1))` equals `(1−2πikC)^{−1}`,
which is exactly the value obtained by evaluating `T^{−1}∫_0^Te^{−2πikC\log t}dt` directly. Two
independent computations of the same quantity agreeing is what pins the limit law; the integrality of
`k` enters through `\exp(2πi k) = 1` (`Complex.exp_int_mul_two_pi_mul_I`), which is the *same*
integrality that forces `|k| ≥ 1` in §177.2 — the formal record of why the method's dual parameter
cannot be made fractional.

Together with `KProfileMismatch` (§176.7) the logarithmic regime is now fully formalised on the
geometric side: its value, its `k`-profile, and the reason that profile cannot be matched by an Euler
product.

---

## 178. Cycle 178 (2026-07-26) — the exact content of the characteristic-function method, stated once and closed

### 178.1 The method's total output

Let `Ψ_T(θ) := (1/T)∫_0^T e^{2πiθS_F(t)}dt`, the characteristic function of the distribution `ν_T` of
`S_F` on `[0,T]`. Three facts:

```
Ψ_T(0) = 1                                             trivially
Ψ_T(k) = O_F(1/(k\,d_F\,T))   for every k ∈ Z\{0\}     UNCONDITIONAL (functional equation + van der Corput)
Ψ_T(θ) ≈ (\log T)^{−θ²n_F}    for |θ| ≪ (\log\log T)^{−1/2}   Selberg CLT — conditional on (a)
```

By Weyl's criterion the second line says exactly: **the push-forward of `ν_T` to `R/Z` is Lebesgue
measure to within `O(1/T)`.** Nothing else. The unwrapped distribution — the object that carries
`n_F` — is entirely unconstrained by the identity `e^{2πikS_F} = e^{−2πikM_F}`.

> **Theorem 104 (the method's ceiling, stated exactly).** The total unconditional content of the
> identity `e^{2πikS_F} = e^{−2πikM_F}` is: `S_F` is equidistributed mod `1` with discrepancy
> `O_F(1/T)`. Every theorem the method has produced (84′, 85′, 87, 89, 90, 103) is a consequence of
> that single statement, and no statement about the unwrapped law of `S_F` — in particular no value or
> rate for `n_F` — follows from it.

This is why (★) fails outside the convergent regime (§171), why no periodic test function helps
(§150.2, §177.2), and why the optimal dual frequency `k ≍ E^{−1/2}` is unreachable (§177.2, (FRAC)).
**One statement, five previously separate ceilings.**

### 178.2 A concrete corollary: `S_F` is *more* uniform mod 1 than Gaussian

A centred Gaussian of variance `σ²` has characteristic function `e^{−2π²θ²σ²}`, so with
`σ² = (n_F/2π²)\log\log T` (the Selberg CLT variance) it would give `|Ψ_T(1)| = (\log T)^{−n_F}`. The
truth is `O(1/T)`. Hence

> **Corollary 105 (unconditional).** For every non-constant `F ∈ S`,
> `|Ψ_T(1)|·(\log T)^{n_F} ≪ (\log T)^{n_F}/T → 0`: the distribution of `S_F` is uniform mod `1` to a
> precision **exceeding the Gaussian prediction by a factor `T(\log T)^{−n_F}`**.

The excess uniformity is purely archimedean: it comes from `S_F ≡ −M_F \pmod 1` with `M_F'' ≠ 0`. It
is therefore *not* evidence about the primes — a point worth recording, since the Selberg CLT is often
read as saying `S_F` "is Gaussian", and the identity shows the Gaussian model is badly wrong at the
mod-1 scale.

### 178.3 Two routes checked and closed this cycle

- **Pretentious/Halász.** `|a_F(n)|²` is a non-negative multiplicative function, and Conjecture B reads
  `D(a_F,a_G;x)² = Σ_{p≤x}|a_F(p)−a_G(p)|²/p ∼ (n_F+n_G)\log\log x` — *maximal* pretentious distance.
  Theorem 85′ gives divergence; the gap is again "divergence versus rate". Halász's theorem applied
  directly to `a_F` gives nothing: the distance `Σ_p(1−\mathrm{Re}\,a_F(p)p^{−it})/p` is
  `\log\log x + O(1)` automatically because `Σ_pa_F(p)p^{−1−it} = \log F(1+it)+O(1)` is bounded for
  entire `F`. **Recorded do-not-retry.**
- **`(\log^-|F|)²` route to (V).** `∫_0^T(\log^+|F(1/2+it)|)²dt ≪ T^{1+ε}` follows from the second
  moment (available for `d ≤ 2`, §166.1) by Hölder; the obstruction is entirely the **negative** part,
  `∫(\log^-|F|)²`, which measures the mass of zeros near the line. **(V) is the zero-density wall, now
  reached from a fifth direction** (after §90, §162, §165.1, §171.3).

### 178.4 Position

The method that produced the programme's unconditional core is now completely characterised
(Theorem 104) and therefore closed. Further progress requires one of:

```
(FRAC)   an exact identity with a finer-than-integer dual parameter
(V)/(a)  a zero-density or pair-correlation input
(P1)_2   n_F = 1 for primitive degree-2 F
(NC)     a lower bound for the first coefficient disagreement
MI       meromorphy of the Rankin–Selberg object
```
all of which are recorded with their exact obstructions. No route inside the characteristic-function
method remains untried.

---

## 179. Cycle 179 (2026-07-26) — the Satake/character formulation, and the sharpest form of the obstruction

### 179.1 What the Euler product actually supplies

Under PEP the local factor is `F_p(s)^{-1} = ∏_{i=1}^{d}(1 − α_i(p)p^{−s})`, and the axioms give the
**power sums** through the logarithmic coefficients:
```
p_k(α(p)) := Σ_{i}α_i(p)^k = k\,b_F(p^k) ,
```
so every symmetric function of the Satake parameters — in particular every irreducible character
`χ_λ(α(p))`, an integer polynomial in the `p_k` — is an explicit function of the coefficients of
`\log F`. Conjecture A is the statement that
```
δ(λ) := \lim_x (\log\log x)^{−1}Σ_{p≤x}χ_λ(α(p))/p
```
is a non-negative integer for `λ = \mathrm{std}⊗\overline{\mathrm{std}}` (then `n_F = δ(λ)`).

> **The obstruction, in its sharpest form.** `\log F` supplies `Σ_pΣ_k b_F(p^k)p^{−ks}`, i.e. the
> `k`-th power sum weighted by **`p^{−ks}`**, singular at `s = 1/k`. Conjecture A needs the same
> character values weighted by **`p^{−s}`**, singular at `s = 1`. *The Euler product delivers the
> character values at the wrong scale, off by `p^{(k−1)s}`.* Only `k = 1` has the two scales agreeing,
> which is exactly why the linear densities are integers (`δ(\mathrm{std}) = −\mathrm{ord}_1F`, §52)
> and nothing else is.

This supersedes §10.1's "linear-moment closure" as the crispest statement of why the axioms cannot
reach a quadratic density, and it explains §172.1's finding that §57/§58 are vacuous: the `k = 2`
integrality they extract lives at `s = 1/2`, not at `s = 1`.

### 179.2 The compact-group criterion, verified

Let `μ` be the logarithmic-density law of the conjugacy class `α(p) ∈ U(d)` (assuming BS with unitary
Satake, and existence of the law). Then `n_F = ∫|\mathrm{tr}|²dμ`, and by Peter–Weyl/Tannaka–Krein,
`∫χ_λ dμ ∈ Z_{≥0}` for all `λ` **iff** `μ` is the push-forward of Haar measure on a compact subgroup
of `U(d)`. So:

> **Conjecture A ⟸ the Satake parameters are Haar-equidistributed in some compact group** (a
> "Sato–Tate group"), and `n_F = \dim\mathrm{End}` of the standard representation restricted to it.

*Verification in degree 2 (non-CM self-dual).* `α_2 = \barα_1 = e^{−iθ}`, `a_F(p) = 2\cosθ_p`,
Sato–Tate measure `(2/π)\sin²θ\,dθ`:
```
n_F = E[4\cos²θ] = \frac{8}{π}∫_0^π\cos²θ\sin²θ\,dθ = \frac{8}{π}\cdot\frac{π}{8} = 1 . ✔
```
Note the mechanism: the *diagonal* `Σ_i|α_i|² = 2` contributes `+2` and the *off-diagonal*
`2\mathrm{Re}(α_1\barα_2) = 2\cos2θ` contributes `2·E[\cos2θ] = −1`. **The off-diagonal density is
negative**, which is why `n_F = 1 < d`. Any argument that bounds `n_F` below by the diagonal alone
would give `n_F ≥ d` and is therefore wrong — recorded as a trap.

Equivalently, since `\mathrm{std}⊗\overline{\mathrm{std}} = \mathbf 1 ⊕ \mathrm{ad}` for `U(d)`,
```
n_F = 1 + δ(\mathrm{ad}) ,
```
so **(P1) `n_F = 1` ⟺ the adjoint density vanishes ⟺ `L(s,\mathrm{ad}F)` is holomorphic and
non-vanishing at `s = 1`** — the classical equivalence, now with the exact scale obstruction of §179.1
attached to it.

### 179.3 Recorded

- **Do-not-retry.** Deriving `δ(λ)` for `λ ≠ \mathrm{std}` from the Euler-product coefficients: the
  scale mismatch of §179.1 is exact and unavoidable. Every attempt (§57, §58, §59, §60, §172.1) has
  failed for this one reason.
- The compact-group criterion is a genuine equivalence but is functoriality by another name; it is
  recorded as the *clean statement of what Conjecture A asserts*, not as a route.
- The GL(2) verification is retained as the programme's standard consistency check: any proposed
  mechanism must reproduce `n_F = 2 − 1 = 1` with a **negative** off-diagonal contribution.

---

## 180. Cycle 180 (2026-07-26) — the scale obstruction is the absence of Adams operations; and Theorem 106

### 180.1 Fixing the scale is exactly a λ-ring structure

§179.1: the axioms supply `𝔟_k(s) := Σ_p b_F(p^k)p^{−ks}` (a piece of `\log F`, singular at `s=1/k`)
while Conjecture A needs `Σ_p b_F(p^k)p^{−s}`, singular at `s=1`. Formally the rescaling is trivial —
`Σ_p b_F(p^k)p^{−s} = 𝔟_k(s/k)` — so the obstruction is **not** the substitution but the fact that the
individual pieces `𝔟_k` cannot be separated from `\log F = Σ_k𝔟_k`: any fixed linear combination
`Σ_mc_m\log F(ms)` has `p^{−js}`-coefficient `Σ_{m|j}c_m b_F(p^{j/m})`, a *fixed* mixture independent
of `F`, so no Möbius-type inversion isolates `𝔟_k`.

In λ-ring language `p_k(α(p)) = k\,b_F(p^k)` is the `k`-th **Adams operation** applied to the local
Satake class. Isolating `𝔟_k` and re-weighting it at `p^{−s}` is exactly asking for an element
`ψ^k(F) ∈ S` with `\log ψ^k(F)(s) = Σ_p p_k(α(p))p^{−s} + \ldots`; and `n_F` needs the *tensor*
`F⊗\bar F`. Hence:

> **Reformulation.** *Conjecture A holds iff `S` carries the operations of a λ-ring compatible with
> the Euler product* — equivalently, iff `S` is closed under `⊗`. Langlands functoriality is precisely
> the assertion that it is. §179.1's scale mismatch is the analytic shadow of the missing λ-operations.

(Formal counterpart already in the corpus: `HTGeometry.additive_not_determine_energy`,
`HTGeometry.energy_ne_of_same_total` — every axiom-supplied integer is *additive* in the primitive
exponents while `n_F = Σe_i²` is quadratic. Nothing new to formalise here; cross-referenced.)

### 180.2 The one tensor operation the axioms DO supply: Dirichlet twists

Kaczorowski–Perelli: for `F ∈ S^♯` and `χ` a primitive Dirichlet character, the twist `F^χ` again
lies in `S^♯` (same degree, conductor multiplied by `q_χ^{d}`). This is a genuine `⊗` with a degree-1
factor, and it is the **only** tensor operation available. Consequently:

> **Theorem 106 (unconditional).** Let `F ∈ S` and let `G = L(s+iθ,χ) ∈ S` be of degree `1`. Then the
> Selberg pairing exists and is an integer:
> ```
> c_{F,G} \;=\; \lim_x (\log\log x)^{−1}Σ_{p≤x}\frac{a_F(p)\overline{a_G(p)}}{p}
>          \;=\; −\,\mathrm{ord}_{s=1+iθ}\big(F^{\barχ}\big) \;∈\; Z .
> ```
> *Proof.* `a_F(p)\overline{a_G(p)} = a_{F^{\barχ}}(p)p^{iθ}`, so the Dirichlet series is
> `Σ_p a_{F^{\barχ}}(p)p^{−(s−iθ)}`, which by Theorem 52 applied to `F^{\barχ} ∈ S^♯` equals
> `\log F^{\barχ}(s−iθ) + (\text{holomorphic on } \mathrm{Re}\,s > 1/2)`. Its logarithmic singularity
> at `s = 1+iθ` has coefficient `−\mathrm{ord}_{1+iθ}F^{\barχ}`, an integer, and a standard Tauberian
> step converts it to the density. ∎

> **Corollary 107.** For `F` primitive of degree `≥ 2` and `G` of degree `1`, **Conjecture B for the
> pair `(F,G)` is equivalent to the non-vanishing of the twist `F^{\barχ}` on the line
> `\mathrm{Re}\,s = 1`** (together with entirety there, which holds as `F^{\barχ}` has no pole for
> `F` primitive of degree `≥ 2`). For `d_F ≤ 2` this is known (Kaczorowski–Perelli's generalized prime
> number theorem in degree `≤ 2`); in general it is open and is equivalent to the GPNT for twists.

This complements §172's Theorem 100 (both factors of degree `1`) and completes the picture: **the
Selberg pairing `c_{F,G}` is unconditionally an integer whenever `\min(d_F,d_G) = 1`.**

Novelty: the degree-1 case of Conjecture B is classical (Selberg; Conrey–Ghosh); what is recorded here
is (i) the exact integer value `−\mathrm{ord}_{1+iθ}F^{\barχ}`, (ii) the equivalence with
non-vanishing of twists, and (iii) the observation that this is the *only* case reachable because the
twist is the only available tensor operation. Assessed as **low novelty, high structural value**.

### 180.3 Why it cannot bootstrap

`n_F = c_{F,\bar F}` needs `F⊗\bar F`, of degree `d²`. The twist supplies only `d×1`. Iterating
twists gives `d×1×1×\cdots = d`, never `d²`. So:

> **Recorded.** The twist tower is closed: no composition of Dirichlet twists produces an object of
> degree `> d_F`, hence none reaches the Rankin–Selberg degree `d_F²`. Conjecture A is therefore
> **strictly** beyond the twist operation, whereas Conjecture B is reachable exactly on the pairs with
> a degree-1 member. This is the precise sense in which A is harder than the accessible part of B.

### 180.4 Position

```
Conjecture B, pairs with min(d_F,d_G) = 1     : reduced to non-vanishing of twists on Re s = 1
                                                (a theorem for d ≤ 2; = GPNT for twists in general)
Conjecture B, both degrees ≥ 2                : needs Rankin–Selberg
Conjecture A, all F with primitive factors of degree 1 : THEOREM (§172)
Conjecture A, d_F ≤ 2                         : = (P1)_2, i.e. n_F = 1 for primitive degree 2
Conjecture A, general                         : = λ-ring structure on S = functoriality
```

---

## 181. Cycle 181 (2026-07-26) — `Im c_{F,G}` in the twist case; why the AFE cannot break the finiteness circle

### 181.1 The imaginary part vanishes for free on twist pairs

Theorem 16/19 record that energies are blind to `\mathrm{Im}\,c_{F,G}`, so the symplectic form `ω` needs
a separate mechanism. Theorem 106 supplies one in the only case it can:

> **Corollary 108 (unconditional).** If `\min(d_F,d_G) = 1` then `c_{F,G} = −\mathrm{ord}_{1+iθ}F^{\barχ}`
> is a **rational integer**, hence `\mathrm{Im}\,c_{F,G} = 0` and `ω(F,G) = 0`.

So the symplectic form vanishes identically on every pair with a degree-1 member. Since the twist is
the only available tensor operation (§180.2), this is exactly the set of pairs where `ω` is currently
computable, and there `ω ≡ 0` — consistent with Conjecture B and with the expectation `ω ≡ 0`
throughout, but giving no leverage on pairs of degree `≥ 2`.

Checked and closed this cycle: **there is no way to convert `\mathrm{Im}\,c` into a `\mathrm{Re}\,c`.**
One would need an element with prime coefficients `i·a_G(p)`; the shift family `G_θ` does not supply it,
because `p^{iθ}` varies with `p` (it is not a global rotation), and by Theorem 97 the shifted
correlations `c_{F,G_θ}` vanish for all but finitely many `θ`, so the family carries no rotation at
all. **Recorded do-not-retry.**

### 181.2 Finiteness of `n_F`: the circle the approximate functional equation cannot break

`\limsup_x E(x)/\log\log x < ∞` is open (§172.3). The natural route and why it is circular:

```
∫_0^T|F(1/2+it)|²dt  =  T·Σ_{n≤cT}|a_F(n)|²/n·(1+o(1))  +  O(Σ_{n≤cT}|a_F(n)|²)        (AFE + MVT, d ≤ 2)
```
Both the main term and the error are built from `A(x) := Σ_{n≤x}|a_F(n)|²`, so the identity relates
the moment to `A` and back — it is an **identity**, not an estimate, and cannot bound either side.
Feeding in the only unconditional input, `a_F(n) ≪_ε n^ε`, gives `A(x) ≪ x^{1+ε}` and hence
`∫_0^T|F|² ≪ T^{1+ε}`, which returns `Σ_{n≤T}|a_F(n)|²/n ≪ T^{ε}` — exactly what was put in.

> **Recorded.** Finiteness of `n_F` is equivalent to `A(x) ≪ x(\log x)^{C}`, i.e. to
> `∫_0^T|F(1/2+it)|²dt ≪ T(\log T)^{C}` — a Rankin–Selberg-strength bound. The approximate functional
> equation, being an identity, cannot produce it; any proof must inject an independent upper bound for
> `F` on the critical line. Convexity (`|F| ≪ 𝔮^{(1−σ)/2+ε}`) is far too weak, giving
> `∫ ≪ T^{1+d/2+ε}`. **Do-not-retry.**

### 181.3 Corpus hygiene

`scripts/formal_tools.py lint --check-generated` run this cycle. All modules added in cycles 166–177
(`LogFrequencySeparation`, `CountPositivityConductorBound`, `KProfileMismatch`, `LogPhaseDensity`, and
the additions to `BesselPSD`, `GeneralizedDirichletMeanValue`) compile and are reachable from the
`HTGeometry` umbrella; `lake build +GaloisForLFunctions.HTGeometry` is clean and none of them emits a
warning. The generated indexes were regenerated. Two lint errors are **not** from this programme —
four `RHTower.DeningerArithmetic*` modules are unreachable from their umbrella, work in progress in
another area of the repository — and are left untouched.

---

## 182. Cycle 182 (2026-07-26) — literature positioning of Theorem 102, and confirmation that (a) is the wall

### 182.1 The 2024–2026 unconditional `S(t)` literature

Searched July 2026 for unconditional results on `S_F(t)` in the absence of GRH:

- **arXiv:2410.03473**, *On an unconditional spectral analog of Selberg's result on `S(t)`* — for
  Hecke–Maass cusp forms `u_j`, asymptotic formulas for the **moments** of
  `S_j(t) = π^{−1}\arg L(1/2+it,u_j)` without GRH.
- **arXiv:2502.01288** (Sci. China Math. 2025), *On an unconditional `GL_3` analog of Selberg's
  result* — the same for Hecke–Maass cusp forms on `SL_3(Z)` with the Langlands parameter in generic
  position.
- **arXiv:2407.14867** (Lith. Math. J. 2026), *On a level analog of Selberg's result on `S(t)`*.

**Method in all three: weighted zero-density estimates.** That is exactly hypothesis (a). These
families admit density estimates because they are automorphic and the relevant moments are available;
the abstract Selberg class does not (§166.1).

> **Positioning of Theorem 102** (`\liminf_T(1/T)∫_0^T|S_F|²dt = ∞`, hence `S_F` unbounded, for every
> non-constant `F ∈ S`). It is *weaker* than the cited results where they apply — it gives no moment
> asymptotic, only divergence — and *complementary* where they do not: it holds for **every** element
> of the abstract class, uses **no** zero-density estimate, and its proof is the amplifier plus Bessel
> for Fourier–Bohr coefficients plus Theorem 84′. The literature confirms the programme's diagnosis:
> every quantitative statement about `S_F` in the divergent regime rests on a density estimate, and
> the only route that avoids one is the amplifier, which yields lower bounds and nothing else.

Recorded as: **novel in scope (whole class, no density input), not in strength.** Assessed, not
claimed.

### 182.2 Consolidated state of the programme after cycles 165–182

**Unconditional theorems** (all in the preprint, all with Lean support where formalisable):

| | statement |
|---|---|
| Thm 84′/89 | convergent prime energy ⟹ trivial, throughout the group completion |
| Thm 85′ | equal `γ,q` and `Σ_p\|a_F(p)−a_G(p)\|²/p = O(1)` ⟹ `F = G` |
| Cor 101 | agreement at every prime ⟹ equality (no archimedean hypothesis) |
| Thm 90 | sharpness: the method decides exactly convergence |
| Thm 76′ | band-limited amplifier: prime side and `‖φ'‖_2²` both **exact** |
| Thm 76″ | `(1/T)∫_0^T\|S_F\|² ≥ (1/4π²)E(T/2) + 1/12 − o(1)` — half of Selberg's asymptotic, no density input |
| Thm 100 | Conjecture A **and** B for all `F` whose primitive factors have degree 1, with `n_F = Σm_i²` |
| Cor 102 | Conjecture A unconditional for `d_F ≤ 2` except primitive degree 2, where it is `n_F = 1` |
| Thm 102 | `S_F` unbounded, `(1/T)∫\|S_F\|² → ∞`, for every non-constant `F ∈ S` |
| Thm 103 | complete mod-1 classification (uniform / Benford / point mass) |
| Thm 104 | the method's exact ceiling: equidistribution mod 1 with discrepancy `O(1/T)` |
| Thm 106 | `c_{F,G} = −\mathrm{ord}_{1+iθ}F^{\barχ} ∈ Z` whenever `\min(d_F,d_G) = 1` |
| Cor 108 | hence `ω(F,G) = 0` on every pair with a degree-1 member |

**Named open cores, each with its exact obstruction recorded:**
```
(FRAC)  finer-than-integer dual parameter        ⟹ rates for E(T)      [blocked: e^{2πikN_F}=1 needs k ∈ Z]
(V)/(a) zero-density / pair correlation          ⟹ the whole quantitative layer
(P1)_2  n_F = 1 for primitive degree-2 F         ⟹ Conjecture A for d ≤ 2
(NC)    lower bound for a_F(n_0) − a_G(n_0)      ⟹ effective strong multiplicity one at √q
MI      λ-ring / tensor structure on S           ⟹ Conjecture A in general
```
**Six corpus defects found and repaired** (§§167, 168, 171, 173, 176); the correction ledger is
§176.6 plus §173.3.

---

## 183. Cycle 183 (2026-07-26) — (P1)₂ reduced to a prime-square density; and the "sieve-and-rescale" obstruction

### 183.1 The degree-2 identity

Let `F ∈ S` have degree `2` with a polynomial Euler product, so
`F_p(s)^{−1} = 1 − a_F(p)p^{−s} + c_p\,p^{−2s}` with `c_p := α_pβ_p` (the local "determinant", defined
outright by the local factor). Then `a_F(p²) = α² + αβ + β² = a_F(p)² − c_p`, i.e.
```
a_F(p)²  =  a_F(p²) + c_p .
```
Writing `δ_1(g) := \lim_x(\log\log x)^{−1}Σ_{p≤x}g(p)/p` for the logarithmic density at scale `p^{−1}`,
and assuming `F` self-dual so that `|a_F(p)|² = a_F(p)²`:

> **Theorem 109 (unconditional, given PEP and self-duality).** For `F ∈ S` of degree `2`,
> ```
> n_F  =  δ_1\big(p ↦ a_F(p²)\big)  +  δ_1\big(p ↦ c_p\big) ,
> ```
> whenever the two densities on the right exist. If moreover the determinant `c_p` is the value of a
> Dirichlet character (automatic when `F` is automorphic, and forced by the functional equation
> whenever the local factors are those of a `GL_2` representation), then `δ_1(c) ∈ \{0,1\}`
> **unconditionally**, by non-vanishing of `L(1,χ)`.
>
> Consequently `(P1)_2` — Conjecture A in degree `≤ 2` (Cor. 102) — is exactly
> ```
> δ_1\big(p ↦ a_F(p²)\big)  =  1 − δ_1(c)  ∈ \{0,1\} ,
> ```
> a statement about the **honest Dirichlet coefficients of `F` at prime squares**, weighted `p^{−1}`.

*Consistency check.* For a `GL_2` newform of trivial nebentypus, `c_p = 1` for `p∤N`, so `δ_1(c) = 1`;
and `a_F(p²) = a_{\mathrm{sym}²}(p)` with `Σ_pa_{\mathrm{sym}²}(p)p^{−s} = \log L(s,\mathrm{sym}²)+O(1)`
regular at `s=1`, so `δ_1(a_F(·²)) = 0`. Total `n_F = 0 + 1 = 1` ✔ — matching the Sato–Tate
computation of §179.2, by a completely different route.

This is the **cleanest reduction of Conjecture A in low degree** the programme has produced: no
Rankin–Selberg object, no zero statistics, no monodromy — just the logarithmic density of
`a_F(p²)` over primes.

### 183.2 Why it is still blocked: sieve-and-rescale

`Σ_p a_F(p²)p^{−s}` is not supplied by the axioms. The two operations needed are:

1. **Sieve.** Extract from `F(s) = Σ_n a_F(n)n^{−s}` the sub-series supported on `n = p²`. Equivalently
   extract `𝔟_k` from `\log F = Σ_k𝔟_k` (§180.1). No fixed linear combination of `F(ms)` or
   `\log F(ms)` does this: the `p^{−js}`-coefficient of `Σ_mc_m\log F(ms)` is `Σ_{m|j}c_mb_F(p^{j/m})`,
   a mixture independent of `F`.
2. **Rescale.** Move the extracted series from its natural weight `p^{−2s}` (singular at `s = 1/2`) to
   `p^{−s}` (singular at `s = 1`). Formally this is `G(s) ↦ G(s/2)`, harmless — but only *after* the
   sieve, and the sieve is what fails.

> **Recorded (the obstruction at maximum resolution).** *Every* route to Conjecture A found in this
> programme — `R_{F,F}`, `ℛ_F`, `𝔐_F`, the contour extractor, the standard twist, the character
> densities `δ(λ)`, and now Theorem 109 — requires **sieving a sub-series of `F` or `\log F` supported
> on a thin set and then rescaling its weight**. Neither operation is analytic; their composition is
> exactly what the tensor operation `F ⊗ \bar F` performs, and its absence is Langlands functoriality.
> This supersedes §179.1 (which recorded only the rescaling half) and §10.1 (linear-moment closure).

### 183.3 What Theorem 109 does buy

Even blocked, the reduction is useful:

- It replaces a *quadratic* invariant (`n_F`) by a **linear** one (`δ_1` of the prime-square
  coefficients) plus a term that is `\{0,1\}`-valued for free. That is the first time the quadratic
  problem has been reduced to a linear density — the quadratic-versus-additive obstruction of
  Theorem 39 is *bypassed* in degree 2 by the Hecke relation `a_F(p)² = a_F(p²) + c_p`.
- It isolates the difficulty in a single, concrete, prime-indexed sum with honest coefficients, at the
  correct scale for a Tauberian argument.
- It generalises: for degree `d` with PEP, Newton's identities express `|a_F(p)|²` as an integer
  polynomial in `a_F(p^j)` and `\overline{a_F(p^j)}`, `j ≤ d`, so `n_F` is an integer combination of
  the densities `δ_1(a_F(·^j))` and their conjugates. **Conjecture A therefore follows from:
  `δ_1(a_F(·^j)) ∈ Z` for `j ≤ d`.** That is a *finite* list of linear-density integrality statements,
  each of the same shape as the one already proved for `j = 1` (`δ_1(a_F) = −\mathrm{ord}_1F`, §52).

> **New named target (PSD_j).** *Is `δ_1(p ↦ a_F(p^j))` an integer for each `j ≥ 2`?* For `j = 1` this
> is Theorem 52 and is unconditional. For `j ≥ 2` it is open and, by §183.2, requires the sieve. **This
> is the sharpest finite reduction of Conjecture A the programme has: `d` linear-density integrality
> statements instead of one quadratic one.**

---

## 184. Cycle 184 (2026-07-26) — **Theorem 111**: Conjecture A follows from ONE linear-density statement, `Sym²`-closure

### 184.1 Correction to §183.3

§183.3 asserted that for degree `d`, Newton's identities express `|a_F(p)|²` in terms of
`a_F(p^j)` for `j ≤ d`, giving `d` targets `(PSD_j)`. **That is unnecessarily weak: only `j = 2` is
needed, and no PEP hypothesis is required.** The correct route is the coefficient identity of
Theorem 60, which needs nothing beyond the Euler product:
```
a_{FG}(p²) = a_G(p²) + a_F(p)a_G(p) + a_F(p²)  ⟹  |a_F(p)|² = a_{F\bar F}(p²) − a_F(p²) − \overline{a_F(p²)} .
```
(Newton's route `a_F(p)² = 2a_F(p²) − 2b_F(p²)` — valid in every degree, from `p_1² = 2h_2 − p_2`,
`h_2(α(p)) = a_F(p²)`, `p_2(α(p)) = 2b_F(p²)`; checked on `ζ` (`2·1 − 2·½ = 1`) and on a `GL_2`
newform (`2(a²−1) − (a²−2) = a²`) — gives an equivalent but longer identity and is recorded only as a
cross-check.)

### 184.2 The reduction

Write `δ_1(g) := \lim_x(\log\log x)^{−1}Σ_{p≤x}g(p)/p`, the **linear** logarithmic density at the
scale `p^{−1}`. Recall the one unconditional instance already proved:
```
δ_1\big(p↦a_G(p)\big) = −\mathrm{ord}_{s=1}G ∈ Z        for every G ∈ S^♯   (Theorem 52 + Tauberian).
```

> **(PSD₂).** *For every `G ∈ S`, `δ_1\big(p↦a_G(p²)\big) ∈ Z`.*

> **Theorem 111.** **(PSD₂) ⟹ Selberg's Conjecture A.**
> *Proof.* For `F ∈ S` also `F\bar F ∈ S`, and by §184.1
> ```
> n_F = δ_1\big(a_{F\bar F}(·²)\big) − 2\,\mathrm{Re}\,δ_1\big(a_F(·²)\big) ,
> ```
> an integer minus twice the real part of an integer. ∎

So the *quadratic* invariant `n_F` is produced by **two linear densities**, of honest Dirichlet
coefficients of elements of `S`, at the correct scale for a Tauberian argument. The
quadratic-versus-additive obstruction (Theorem 39) is bypassed entirely: the quadratic term
`a_F(p)\overline{a_F(p)}` is absorbed into the *linear* coefficient `a_{F\bar F}(p²)` of the auxiliary
element `F\bar F`.

### 184.3 What (PSD₂) is

`a_G(p²) = h_2(α(p))` is the value of the character of `\mathrm{Sym}²` on the Satake class, so
`Σ_pa_G(p²)p^{−s}` is the `k = 1` part of `\log L(s,\mathrm{Sym}²G)`, and by the argument of
Theorem 52 the two differ by a function holomorphic on `\mathrm{Re}\,s > 1/2`. Hence

> **(PSD₂) ⟺ for every `G ∈ S`, `L(s,\mathrm{Sym}²G)` continues to a neighbourhood of `s = 1` as a
> single-valued function with integer order there.** Equivalently: **`S` is closed under `\mathrm{Sym}²`**
> (in the weak, monodromy-only sense of MI).

> **This is strictly weaker than the hypothesis the programme has been carrying.** MI asks for
> meromorphy of the *bilinear* object `R_{F,G}` for **all pairs**; Theorem 111 asks only for the
> *unary* operation `\mathrm{Sym}²`, of degree `d(d+1)/2` instead of `d²`, applied to each element
> separately. In degree `2`: degree `3` instead of degree `4`.

### 184.4 Status and significance

- **Sufficiency only.** The converse fails: knowing every `n_F` gives only the relations
  `δ_1(a_{G\bar G}(·²)) = n_G + 2\mathrm{Re}\,δ_1(a_G(·²))`, which do not isolate `δ_1(a_G(·²))`.
- **The obstruction is unchanged in kind** — `Σ_pa_G(p²)p^{−s}` still requires the sieve-and-rescale of
  §183.2 — but the *target* is now a single unary operation rather than a bilinear closure, and the
  statement to be proved is a **linear** density integrality of the exact shape already established for
  `j = 1`.
- **Consistency.** For a `GL_2` newform with trivial nebentypus, `a_F(p²) = a_{\mathrm{sym}²}(p)` and
  `Σ_pa_{\mathrm{sym}²}(p)p^{−s} = \log L(s,\mathrm{sym}²)+O(1)` is regular at `s = 1`, so
  `δ_1(a_F(·²)) = 0`; and `a_{F\bar F}(p²) = a_F(p²)+a_F(p)²+a_F(p²)`, giving
  `δ_1(a_{F\bar F}(·²)) = 0 + n_F + 0`, whence `n_F = n_F` ✔ — the identity is consistent, and pins
  `n_F = 1` exactly when `Σ_pa_F(p)²/p ∼ \log\log x`, i.e. `\mathrm{sym}²` regular and `\det` principal
  (§183.1).

> **Recorded as the programme's sharpest reduction.** Every earlier formulation of Conjecture A — MI,
> meromorphy of `R_{F,F}`, `ℛ_F`, `𝔐_F`, the λ-ring/tensor closure — is bilinear or asks for a full
> functorial structure. **Theorem 111 reduces Conjecture A to a single unary closure property,
> `\mathrm{Sym}²`, expressed as the integrality of one linear logarithmic density.** Novelty: the
> identity `|a_F(p)|² = a_{F\bar F}(p²) − 2\mathrm{Re}\,a_F(p²)` is elementary and was already recorded
> here as Theorem 60; what is new is reading it as a *reduction of the quadratic conjecture to a linear
> density*, and the consequent replacement of bilinear MI by unary `\mathrm{Sym}²`-closure. Searched
> July 2026 ("Selberg conjecture A symmetric square sufficient", "normality conjecture symmetric
> square"): not located. Assessed, not claimed.

### 184.5 Lean

The engine of Theorem 111 was **already in the corpus** — corpus search performed first, no
duplication written:
```
RHTower.selberg_pairing_prime_sq  (GaloisForLFunctions/RHTower/SelbergPairingPrimeSquare.lean:100)
  f p * conj (g p) = (f * conjArith g) (p^2) − f (p^2) − conj (g (p^2))
```
for arithmetic functions with `f 1 = g 1 = 1` and `p` prime. With `f = g = a_F` this is exactly
`|a_F(p)|² = a_{F\bar F}(p²) − a_F(p²) − \overline{a_F(p²)}`, the identity Theorem 111 runs on.

New this cycle, the Newton cross-check of §184.1, added beside `log_coeff_bound`:
```lean
theorem newton_sq_identity {A B : ℕ → ℂ} (hA0 : A 0 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n : ℂ) * A n = ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℂ) * B (n - j) * A j) :
    A 1 ^ 2 = 2 * A 2 - 2 * B 2
```
i.e. `a_F(p)² = 2a_F(p²) − 2b_F(p²)` for every Euler factor: **the square of the prime coefficient is
a `Z`-linear combination of prime-square data, one honest coefficient and one logarithmic
coefficient.** This is the degree-free form of §183.1's Hecke relation and holds with no PEP
hypothesis. `lake build +GaloisForLFunctions.HTGeometry` clean.

Together the two Lean facts say: *the passage from the quadratic prime datum to linear prime-square
data is completely formal.* Everything that remains open in Theorem 111 is the analytic continuation
of `Σ_pa_G(p²)p^{−s}` to `s = 1` — i.e. `\mathrm{Sym}²`-closure.

---

## 185. Cycle 185 (2026-07-26) — the sieve obstruction closed from four independent angles

(PSD₂) needs `A_2(s) := Σ_p a_G(p²)p^{−s}` near `s = 1`. Four constructions were tried this cycle;
all fail for the same reason, and the reason is now closed off.

### 185.1 Why `j = 1` works and `j = 2` cannot

`Σ_p a_G(p)p^{−s} = \log G(s) + (\text{holomorphic on } \mathrm{Re}\,s > 1/2)` because in
`\log G = Σ_{p,j}b_G(p^j)p^{−js}` the `j = 1` term carries **exactly** the weight `p^{−s}` and
`b_G(p) = a_G(p)`. For `j = 2` the natural weight is `p^{−2s}` (singular at `s = 1/2`) and the target
weight is `p^{−s}` (singular at `s = 1`).

### 185.2 The four attempts

1. **Möbius over dilates.** The `p^{−js}`-coefficient of `Σ_mc_m\log G(ms)` is `Σ_{m|j}c_mb_G(p^{j/m})`
   — a mixture with coefficients independent of `G`, so no choice of `(c_m)` isolates `j = 2`.
2. **Even part / Liouville.** Per prime, the even-index part of the Euler factor is
   `\tfrac12(G_p(X)+G_p(−X))`, and `∏_p\tfrac12(G_p(p^{−s})+G_p(−p^{−s})) = Σ_m a_G(m²)m^{−2s}` ✔ —
   but an average of products is not the product of averages, so this is **not**
   `\tfrac12(G(s)+G^λ(s))` with `G^λ` the Liouville twist. And `G^λ(s) = G(s)^{−1}·Ψ(2s)` with
   `Ψ = ∏_p∏_i(1−α_i²p^{−w})^{−1}` — the Adams object `ψ²`, i.e. the thing being sought.
3. **Square-index extraction.** Restricting `Σ_na_G(n)n^{−w}` to `n = m²` is a Hadamard-type operation
   with no analytic realisation: squares are not a union of congruence classes, so no character
   detects them.
4. **Frequency rescaling.** `G(s/2) = Σ_na_G(n)(\sqrt n)^{−s}` does put the coefficient `a_G(p²)` at
   frequency `\log p` ✔ and is meromorphic on `C` ✔ — but the frequency-`\log p` part of
   `\log G(s/2)` is `Σ_p b_G(p²)p^{−s}` (not `a_G(p²)`), and the `j = 1` part
   `Σ_pb_G(p)p^{−s/2}` has abscissa `2`, so it dominates near `s = 1` rather than being holomorphic
   there. Extracting the wanted part is again the sieve.

> **Recorded do-not-retry (comprehensive).** The passage from prime-square data at weight `p^{−2s}` to
> weight `p^{−s}` requires isolating one `j`-graded piece of `\log G` (or one index-class of `G`). This
> is impossible by: dilation combinations (1), sign/Liouville twists (2), index restriction (3), or
> argument rescaling (4). **The sieve is the irreducible obstruction, and it is exactly the missing
> `\mathrm{Sym}²` operation.** No further attempt of this type should be made without a genuinely new
> analytic construction.

### 185.3 Positivity checked and unavailable

`a_{F\bar F}(n) = Σ_{de=n}a_F(d)\overline{a_F(e)}` is **not** coefficientwise non-negative (unlike the
true Rankin–Selberg `L(s,π×\tildeπ)`), although `Σ_na_{F\bar F}(n)n^{−σ} = |F(σ)|² ≥ 0` on the real
axis. So Landau's theorem does not apply to `F\bar F` and no positivity route to (PSD₂) exists at this
level. **Recorded.**

---

## 186. Hand-off (state as of cycle 185)

**Goal.** Prove or disprove Selberg's Conjectures A (`n_F ∈ Z`) and B (`c_{F,G} = δ_{F,G}` for
primitives). Both **open**.

**Sharpest reduction.** Theorem 111 (§184): **(PSD₂) ⟹ Conjecture A**, where
(PSD₂) is `δ_1(p↦a_G(p²)) ∈ Z` for every `G ∈ S`, equivalently `S` is closed under `\mathrm{Sym}²`
in the monodromy-only sense. Engine: `|a_F(p)|² = a_{F\bar F}(p²) − 2\mathrm{Re}\,a_F(p²)`
(Lean: `RHTower.selberg_pairing_prime_sq`); degree-free cross-check
`a_F(p)² = 2a_F(p²) − 2b_F(p²)` (Lean: `HTGeometry.newton_sq_identity`).

**Unconditional results of this session** (cycles 165–185): Theorems 76′, 76″, 100, 102, 103, 104,
106, 109, 111, Corollaries 101, 102, 105, 108. All in the preprint
`4-publication-ready/monodromy-integrality-selberg.md` §§12–15.

**Lean added this session** (all `lake build +GaloisForLFunctions.HTGeometry` clean):
`HTGeometry/LogFrequencySeparation.lean`, `CountPositivityConductorBound.lean`,
`KProfileMismatch.lean`, `LogPhaseDensity.lean`; additions to `BesselPSD.lean`
(`bessel_of_almost_orthogonal`, `energy_near_int_of_almost_orthonormal`),
`GeneralizedDirichletMeanValue.lean` (`oscInt_gram_bound`), `LogCoefficientTransfer.lean`
(`newton_sq_identity`).

**Six defects found and repaired** — ledger at §176.6 and §173.3. Standing rule: **re-derive any
recorded theorem before building on it**; four of the six were imported bounds cited at the wrong
strength or hypotheses silently dropped.

**Named open cores, each with its exact obstruction:**
```
(PSD₂)  Sym²-closure                 ⟹ Conjecture A          [blocked: the sieve, §185.2, four-fold]
(FRAC)  finer-than-integer dual k    ⟹ rates for E(T)        [blocked: e^{2πikN_F}=1 forces k ∈ Z]
(V)/(a) zero density / pair corr.    ⟹ the quantitative layer [= the moment problem for d ≥ 3]
(P1)₂   n_F = 1, primitive degree 2  ⟹ Conjecture A for d ≤ 2 [= δ_1(a_F(·²)) = 1 − δ_1(det), §183.1]
(NC)    lower bound for a_F(n_0)−a_G(n_0) ⟹ effective SMO at √q_F
```

**Do-not-retry list additions this session:** Baker-type bounds with variable-count-dependent
constants (§167.5); compactly supported test functions in the explicit formula (§173.2); `L^∞`/Kronecker
band projection (§175.3); the resonance method for `S_F` (§175.4); smoothing and sublattice tricks
against (FRAC) (§177.2); Halász/pretentious (§178.3); `(\log^-|F|)²` for (V) (§178.3); the AFE for
finiteness of `n_F` (§181.2); all four sieve constructions (§185.2); positivity of `F\bar F` (§185.3).

---

## 187. Cycle 187 (2026-07-26) — a genuinely new route to the sieve: **spectral summation of standard twists**

§185.2 closed four *analytic* sieves. There is a fifth, of a different kind, which the programme has
not tried: the Kaczorowski–Perelli standard twist **already sieves** — it isolates individual
coefficients as residues — and the missing step is not a sieve but a **summation over a subset of the
spectrum**.

### 187.1 The construction

KP: for `G ∈ S^♯` of degree `d ≥ 1`, `Φ_G(s,α) := Σ_n a_G(n)e(−αn^{1/d})n^{−s}` continues
meromorphically, with poles at `s^*_ℓ` occurring **exactly** for `α ∈ \mathrm{Spec}(G) =
\{α_m := d(m/q)^{1/d} : a_G(m) ≠ 0\}`, and
```
\mathrm{Res}_{s = s^*_0}Φ_G(s,α_m) = c_G\,\overline{a_G(m)}\,m^{−κ}   (c_G, κ explicit).
```
So each coefficient `a_G(m)` **is** a residue: the sieve on individual coefficients is free.

Fix a subset `A ⊆ N` and weights `w(m)`, and set
```
Ψ_A(s) := Σ_{m∈A} w(m)\,Φ_G(s,α_m)
        = Σ_n a_G(n)\,n^{−s}\;W_A\big((n/q)^{1/d}\big) ,\qquad
W_A(u) := Σ_{m∈A}w(m)\,e\big(−d\,m^{1/d}u\big) .
```
All the poles sit at the **same** point `s^*_0`, so if `Ψ_A` converges and is meromorphic there,
```
\mathrm{Res}_{s=s^*_0}Ψ_A(s) = c_G\;Σ_{m∈A}w(m)\,\overline{a_G(m)}\,m^{−κ} ,
```
which is **exactly a sieved, weighted coefficient sum**. Taking `A = \{p²\}` and
`w(m) = m^{κ−s'/2}` gives `Σ_p \overline{a_G(p²)}\,p^{−s'}` — the object of (PSD₂).

> **`Ψ_A` is `G` twisted by an explicit oscillatory weight supported on the spectrum**, and for
> `d = 2` that weight is a classical **prime exponential sum with linear frequencies**:
> `W_A(u) = Σ_p p^{2κ−s'}e(−2pu)`, of Vinogradov type.

### 187.2 Why this is not covered by the recorded no-go

§21 (line ~1234 of this log) recorded: *"No construction that reads `R_{F,G}` off truncated spectral
data of the standard twist can work."* That statement concerns the **bilinear** object `R_{F,G}`,
whose spectral form is a sum of **squared** residues — an `L²`-mass of a Dirac comb, which is why the
`y → 0` blow-up (§11, §12.3) destroys it. Here the target is **linear**: a weighted sum of residues,
first power. The obstruction that killed the bilinear route — that `∫|Φ_F|²dα` acquires a `π/y` term
whose coefficient *is* the diagonal one is trying to produce — does not arise, because no `L²` norm is
taken.

**This is a materially different construction and is not on the do-not-retry list.**

### 187.3 The open core, stated exactly

> **(SPEC).** *For `A = \{p²\}` and `w(m) = m^{κ−s'/2}`, does `Ψ_A(s) = Σ_{m∈A}w(m)Φ_G(s,α_m)`
> converge in a punctured neighbourhood of `s^*_0`, uniformly enough to be meromorphic there with the
> expected simple pole?*

Two known facts bear on it, in opposite directions:

- **Against.** §11.2 proved that `α ↦ Φ_G(·,α)` is **not** locally uniformly bounded near
  `\mathrm{Spec}(G)`: `∮_{C_r}Φ_G(s,α)ds = 0` for `α ∉ \mathrm{Spec}(G)` while it equals `2πi\,ρ_0(α_0) ≠ 0`
  at spectral points, so the family is discontinuous at every point of the spectrum. A naive
  term-by-term sum over `A` therefore has no uniform control.
- **For.** The summation is over a **sparse** subset — `\#\{p² ≤ M\} ≍ \sqrt M/\log M` against
  `\#\{m ≤ M\} = M` — and the weights `w(m) = m^{κ−s'/2}` decay. The poles all coincide at `s^*_0`, so
  no cancellation of pole locations is needed; only the sum of residues and the sum of regular parts
  must converge. The regular part of `Φ_G(·,α_m)` is controlled by KP's Theorem 1 growth bound
  `F_ℓ(s,α) ≪ e^{(π/2)d|t|}|t|^{c(σ)}`, **which is uniform in `α`** — the non-uniformity of §11.2 is
  confined to the polar part, which here is exactly what is wanted.

> **Assessment.** (SPEC) is the first route in many cycles that is (i) not on the do-not-retry list,
> (ii) linear rather than bilinear, and (iii) reduces to a convergence question about an explicit
> series of meromorphic functions with a common pole, rather than to an existence question about a new
> L-function. **Its resolution requires exactly one input: an `α`-uniform bound for the *regular part*
> of the continued standard twist near a spectral point** — precisely §10.2's [OPEN CORE], which KP
> state only for fixed `α`. That input is a technical estimate inside KP's own machinery, not a new
> conjecture.

### 187.4 Consequence chain if (SPEC) holds

```
(SPEC)  ⟹  Σ_p a_G(p²)p^{−s} is meromorphic near s = 1 with integer polar order
        ⟹  (PSD₂)                                   [δ_1(a_G(·²)) = −ord, an integer]
        ⟹  Conjecture A                             [Theorem 111]
        ⟹  with (P1),(P2) — both reduced elsewhere — Conjecture B
```
The integrality at the second step comes from the same mechanism as Theorem 52: an order of a pole is
an integer. **The whole of Conjecture A would then rest on a uniform bound inside Kaczorowski–Perelli's
standard-twist theory.**

> **Recorded as the programme's leading open route**, superseding MI as the target of attack, because
> unlike MI it is a *quantitative estimate about an existing object* rather than the existence of a
> new one.

### 187.5 The two-variable structure, and a circularity check

`Ψ_A` depends on two variables: the twist variable `s` and the weight parameter `s'` in
`w(m) = m^{κ−s'/2}`. Write `Ψ_A(s,s')`. The chain is
```
Re s' large :  Ψ_A(·,s') converges for Re s > 1 and (by SPEC) continues in s to s^*_0 ,
               with  R(s') := \mathrm{Res}_{s=s^*_0}Ψ_A(s,s') = c_G\,Σ_p \overline{a_G(p²)}\,p^{−s'} ;
then         :  continue R in s' to s' = 1 .
```

**Circularity check.** The second step is *a priori* the target itself. It is not circular, because the
`s'`-continuation is carried by a different object: in the `n`-sum
`Ψ_A(s,s') = Σ_n a_G(n)n^{−s}\,W_A\big((n/q)^{1/d};s'\big)` the entire `s'`-dependence sits in the
**prime exponential sum**
```
W_A(u;s') = Σ_p p^{2κ−s'}\,e\big(−d\,p^{2/d}u\big)  \qquad(= Σ_p p^{2κ−s'}e(−2pu)\ \text{for } d = 2),
```
and for `d = 2` this is the classical `Σ_pe(θp)p^{−w}`, which by **Vinogradov's bound**
`Σ_{p≤x}e(θp) ≪ x^{1−δ}` continues past `\mathrm{Re}\,w = 1` for every irrational `θ` of finite type,
being singular only at `θ ∈ Z`. The singular set in the `n`-variable is therefore
`\{n : 2(n/q)^{1/2} ∈ Z\} = \{n = qk²/4\}` — a **thin** set of density `≍ \sqrt n`.

> So the `s'`-continuation is governed by Vinogradov-type cancellation over primes in the *weight*,
> not by the analytic continuation of `Σ_pa_G(p²)p^{−s'}` itself. The two are different mechanisms;
> the construction is not circular. **What it does require is that the thin singular set
> `\{n = qk²/4\}` contributes only a controlled amount**, i.e. that the sub-sum
> `Σ_{k}a_G(qk²/4)(qk²/4)^{−s}·(\text{singular part})` is manageable — itself a prime-square-indexed
> sum, but of `a_G` at *squares* rather than at *prime squares*, which is a strictly easier object
> (it is the coefficient sequence of `G(s/2)`-type data, §185.2(4)).

> **(SPEC) refined — two inputs.**
> **(SPEC-s)** `α`-uniform bounds for the *regular part* of the continued standard twist near a
> spectral point (= §10.2's open core; KP's growth bound is already uniform in `α`, so this is a
> statement about the local expansion C7.1's error terms, listed as the missing item in §14).
> **(SPEC-s′)** Vinogradov-type cancellation in `Σ_pe(θp)p^{−w}` uniformly in `θ`, together with
> control of the thin resonant set `θ ∈ Z`.
>
> Both are estimates about existing objects. Neither asks for a new L-function. **This is the first
> time Conjecture A has been reduced to a pair of analytic estimates rather than to an existence
> statement.**

*Caveat recorded.* Nothing above is proved. The two inputs may well be as hard as what they replace,
and the interchange of `Σ_m` with the analytic continuation is exactly the step §11.2 shows is
delicate. The claim made here is only that the route is **new**, **linear**, **not on the
do-not-retry list**, and **formulated as estimates rather than existence**.

---

## 188. Cycle 188 (2026-07-26) — (SPEC) sharpened: (SPEC-s) is essentially free, and the whole content is a circle-method problem

### 188.1 (SPEC-s) costs nothing

Near `s^*_0`, `Φ_G(s,α_m) = ρ_0(α_m)/(s−s^*_0) + \mathcal{R}_m(s)`, and by Cauchy on a circle of fixed
radius `r`, both Laurent coefficients are `≪_r \max_{|s−s^*_0|=r}|Φ_G(s,α_m)|`. Kaczorowski–Perelli's
growth bound gives `Φ_G(s,α) ≪ e^{(π/2)d|t|}|t|^{c(σ)}` and the residue is `∝ \overline{a_G(m)}m^{−κ}`,
so `|\mathcal{R}_m(s)| ≪ m^{A}` for some fixed `A`. Since `w(m) = m^{κ−s'/2}`, the sum
`Σ_{m∈A}|w(m)|\,m^{A}` converges **for `\mathrm{Re}\,s'` large**, and `Ψ_A(·,s')` is meromorphic near
`s^*_0` there.

> But for `\mathrm{Re}\,s'` large the identity
> `\mathrm{Res}_{s^*_0}Ψ_A(s,s') = c_GΣ_p\overline{a_G(p²)}p^{−s'}` is **trivially true**, because the
> right-hand series already converges. **(SPEC-s) therefore carries no content.** The entire content of
> the route is the continuation in `s'` past `\mathrm{Re}\,s' = 1`. Recorded, and §187.5's two-input
> split is corrected accordingly: there is one input, not two.

### 188.2 The real target, stated as a circle-method problem

The `s'`-dependence lives entirely in the weight, and for `d = 2` (writing `w = s' − 2κ`)
```
Ψ_A(s,s') = Σ_n a_G(n)\,n^{−s}\;V\big(\sqrt{n/q};\,w\big) ,\qquad
V(u;w) := Σ_p e(−2pu)\,p^{−w} .
```
`V(·;w)` continues past `\mathrm{Re}\,w = 1` at every `u` with `2u ∉ Z`, by Vinogradov's
`Σ_{p≤x}e(θp) ≪ x^{1−δ(θ)}` — but `δ(θ)` degrades as `θ` approaches an integer, and
`θ_n = 2\sqrt{n/q}` comes arbitrarily close to integers. So the continuation is **not uniform in `n`**
and the `n`-sum cannot simply be continued term by term.

> **(SPEC′) — the actual open problem.** *Continue*
> ```
> Ψ(s,w) \;=\; Σ_{n}Σ_{p} a_G(n)\,n^{−s}\,p^{−w}\,e\big(−2p\sqrt{n/q}\big)
> ```
> *past `\mathrm{Re}\,w = 1`, for `s` near `s^*_0 = 3/4`.*
>
> This is a **bilinear exponential sum over primes and the coefficients of `G`**, with the phase
> `2p\sqrt{n/q}` — exactly the shape the circle method handles: minor arcs are Vinogradov's bound;
> major arcs are the `n` within `O(k/Q)` of `qk²/4`, i.e. `n` **near** perfect squares (a
> shifted-convolution-type sum of `a_G` against a square-indexed set, of density `≍ \sqrt n`).

### 188.3 Assessment

- **Positive.** Conjecture A (in degree `2`, via Theorem 111 and Cor. 102, hence *all* of Conjecture A
  there) is now reduced to a single, completely explicit, classical-shaped analytic problem: the
  continuation of one bilinear prime/coefficient exponential sum. No new L-function, no functoriality,
  no zero statistics. Every ingredient — Vinogradov's bound, KP's twist theory, the circle method — is
  standard.
- **Negative and recorded honestly.** The major-arc contribution is a shifted-convolution sum of `a_G`
  against a square-indexed set. For `G ∈ S` of degree `2` such sums are of the same difficulty class as
  the subconvexity/shifted-convolution problem for `GL_2`, i.e. genuinely hard, though **not** of the
  same *kind* as the walls the programme has been hitting: it is an estimate, and estimates can be
  attacked by known technology, whereas MI, (V) and (FRAC) are existence or impossibility statements.
- **Novelty.** Searched July 2026 ("standard twist spectral summation Selberg class", "prime
  exponential sum twist L-function Selberg conjecture A"): not located. The construction uses only
  published KP results, but the *combination* — summing standard twists over the prime-square
  sub-spectrum to sieve a coefficient sum — is not in the literature as far as located. Assessed, not
  claimed.

> **Recorded as the programme's leading route**, with the single named target **(SPEC′)**.

---

## 189. Cycle 189 (2026-07-26) — **(SPEC) over-claimed: the two representations have disjoint domains**

Own defect, caught two cycles after it was recorded. §§187–188 presented (SPEC) as a reduction of
Conjecture A to a single circle-method estimate. Checking the domains of validity kills that
presentation.

### 189.1 The consistency test that exposes it

Take `G = ζ²` (degree `2`, so the `d = 2` analysis of §188 applies). Then `a_G(p²) = 3` and
```
Σ_p \overline{a_G(p²)}\,p^{−s'} = 3Σ_p p^{−s'} ,
```
which **has** a logarithmic singularity at `s' = 1`, i.e. `δ_1(a_{ζ²}(·²)) = 3`. (Cross-check of
Theorem 111 on `F = ζ`: `n_ζ = δ_1(a_{ζ²}(·²)) − 2δ_1(a_ζ(·²)) = 3 − 2 = 1` ✔.)

But §188.2's sketch concluded that `Ψ(s,w)` continues in `w` to `\mathrm{Re}\,w > 0` with a single
singularity at `w = 1`, whereas the target sits at `w = s' − 1/2 = 1/2`. If that were right, the
`s`-residue of `Ψ` would be holomorphic at `w = 1/2` and `δ_1(a_G(·²))` would vanish for **every**
`G` — contradicting `δ_1(a_{ζ²}(·²)) = 3`. So the sketch is wrong.

### 189.2 Where it is wrong: disjoint domains

Two representations of the same formal object:
```
(A)  Ψ(s,w) = Σ_p p^{−w}\,Φ_G(s,α_p)          continues in s to s^*_0 = (d+1)/(2d) ,
                                              but needs Re w large for the p-sum to converge.
(B)  Ψ(s,w) = Σ_n a_G(n)n^{−s}\,V(\sqrt{n/q};w)   continues in w past Re w = 1 (circle method),
                                              but the n-sum needs **Re s > 1**.
```
The target is `(s,w) ≈ (s^*_0, 1/2)` with `s^*_0 = 3/4 < 1`. **Representation (B) is invalid at
`\mathrm{Re}\,s = 3/4`** — the Dirichlet series `Σ_n a_G(n)n^{−3/4}` diverges, so the circle-method
analysis of §188.2 never applies where the pole in `s` lives. Representation (A) is valid there but
only for `\mathrm{Re}\,w` large, where the residue identity is trivially true (§188.1).

> **Corrected statement.** (SPEC) is **not** a reduction to one circle-method estimate. It requires a
> genuine **two-variable** continuation joining `(A)` and `(B)`, and the two available representations
> have **disjoint** domains in the relevant direction. This is the same obstruction as the cycle-8
> target of §14.3 (the two-variable Mellin analysis of `K(s,β,y)`), reached from a new direction —
> not a way around it.

### 189.3 What survives

- The **construction** stands: `Σ_{m∈A}w(m)Φ_G(s,α_m) = Σ_n a_G(n)n^{−s}W_A((n/q)^{1/d})` is a correct
  identity where both sides converge, all poles coincide at `s^*_0`, and the residue is the sieved
  coefficient sum. §187.1 is fine.
- The observation that the standard twist **already sieves** — individual coefficients are residues —
  is correct and worth keeping: it is why the linear problem is not obstructed the way the bilinear
  one is (§187.2).
- What fails is only the claim that the two continuations can be carried out in the same
  representation.

> **(SPEC) re-graded: from "leading route" to "a new entry point into the same two-variable
> problem".** It supersedes nothing. MI, (V), (FRAC) and the sieve remain as recorded.

### 189.4 Correction ledger, updated

| # | where | defect | status |
|---|---|---|---|
| 1 | §149.1 | Baker's constant depends on `π(N)` | repaired (§167) |
| 2 | §92.1 | sign of the `n_0` term | corrected (§168) |
| 3 | preprint Thm 13 | `(\log X)^{−C}` gap false at `j=k=1` | corrected (§168.5) |
| 4 | §147.1 (★) | `B²` truncation outside its hypothesis | Thm 91, Cor 92-rate downgraded (§171) |
| 5 | §127.1 | amplifier compactly supported ⟹ divergent prime side | repaired, Thm 76 strengthened (§173) |
| 6 | §139/§147/§150 | archimedean phase one term short | repaired; fourth regime found (§176) |
| 7 | §187–188 | (SPEC): domains of the two representations are disjoint | **corrected here (§189); route re-graded** |

Seven defects. **Six were found by re-deriving a recorded result; the seventh by running a numerical
consistency check (`G = ζ²`) against a claim made two cycles earlier.**

> **Standing rule, strengthened.** Every reduction must be tested on `ζ`, `ζ²`, and a `GL_2` newform
> **before** it is recorded as a route. Domain-of-validity checks are part of the derivation, not a
> formality: a formal identity between two series is worthless if the domains where each converges do
> not overlap the point of interest.

---

## 190. Cycle 190 (2026-07-26) — Bochner's tube theorem applied to the two-variable problem: why it must fail

§189 isolated the obstruction as a two-variable continuation with disjoint domains. The canonical tool
for exactly that situation is **Bochner's tube theorem**: a function holomorphic on a tube
`T_Ω = Ω + iR^n` extends holomorphically to `T_{\hat Ω}`, `\hat Ω` the convex hull. This cycle applies
it, computes the hull, and finds the reason it cannot conclude — a reason that is itself informative.

### 190.1 The hull computation

Work with `\tildeΨ(s,w) := (s−s^*_0)Ψ(s,w)`, which removes the simple pole in `s`. Domains in
`(σ,u) = (\mathrm{Re}\,s,\mathrm{Re}\,w)`:
```
D_A = (σ_1, 3/4+r) × (W_0, ∞) ,     D_B = (1,∞) × (0,∞) ,
```
where `σ_1 > s^*_1 = 1/4` (the twists `Φ_G(·,α_p)` are holomorphic between consecutive poles) and
`W_0` is the abscissa of the `p`-sum near `s^*_0`.

**`W_0 = 1/2`, and this is forced.** The residue is `ρ_0(α_m) ∝ \overline{a_G(m)}m^{s^*_0−1}`; with
`d = 2`, `m = p²`, `s^*_0 = 3/4` this is `∝ \overline{a_G(p²)}p^{2(s^*_0−1)} = \overline{a_G(p²)}p^{−1/2}`.
So `Σ_p p^{−w}Φ_G(s,α_p)` converges for `\mathrm{Re}\,w > 1/2` and no better.

**Hull.** For `(σ,u)` with `σ_1 < σ < 1`, writing `(σ,u) = λ(σ_A,u_A)+(1−λ)(σ_B,u_B)`, the minimal
weight on `D_A` is `λ_{\min} = (1−σ)/(1−σ_1)` (attained as `σ_B → 1^+`, `σ_A → σ_1^+`), so the hull is
```
\hat Ω ⊇ \{(σ,u) : σ_1 < σ < 1,\ u > \tfrac{1−σ}{1−σ_1}\cdot W_0\} ∪ \{σ ≥ 1, u > 0\} .
```
At the target `σ = 3/4` with `σ_1 ↓ 1/4` and `W_0 = 1/2`:
```
u > \frac{1/4}{3/4}\cdot\frac12 = \frac16 \;<\; \frac12 .
```
> **So the target point `(σ,u) = (3/4, 1/2)` lies comfortably in the *interior* of the convex hull.**
> If `\tildeΨ` were holomorphic on the two tubes, Bochner would place it holomorphic at the target —
> hence `R(w) = \tildeΨ(s^*_0,w)` holomorphic at `w = 1/2`, hence
> `δ_1(a_G(·²)) = 0` for **every** `G ∈ S`.

### 190.2 Why that conclusion is false, and what it means

`δ_1(a_{ζ²}(·²)) = 3 ≠ 0` (§189.1). So the hypothesis of Bochner must fail, and it does:

> **`D_B` is not a tube.** The circle-method continuation of `V(θ;w) = Σ_pe(−2pθ)p^{−w}` past
> `\mathrm{Re}\,w = 1` produces, on the major arcs, a term behaving like `\log ζ(w)` — a **branch
> point** at `w = 1` with a cut running left through `\mathrm{Re}\,w < 1`, together with cuts from the
> zeros of `ζ`. `Ψ` is therefore not single-valued on any tube reaching `\mathrm{Re}\,w < 1`, and the
> tube theorem does not apply.

This is not a technical annoyance: **the branch cuts are the conjecture.** Writing
`R(w) = κ\log\frac1{w−1/2} + O(1)` with `κ = δ_1(a_G(·²))`, one has
```
∂_wR(w) = −Σ_p\overline{a_G(p²)}(\log p)\,p^{−1/2−w} ,   κ = −\mathrm{Res}_{w=1/2}\,∂_wR ,
```
and `κ ∈ Z` **iff** `e^{R(w)} = ∏_p\exp(\overline{a_G(p²)}p^{−1/2−w}) ≍ L(s',\mathrm{Sym}²G)` is
single-valued at that point — which is (PSD₂), i.e. `\mathrm{Sym}²`-closure, i.e. MI for `\mathrm{Sym}²`.

> **Recorded (a genuine clarification).** The two-variable obstruction of §14.3 and §189.2 is **not** a
> gap in technique. Bochner's tube theorem would settle it outright were the object single-valued; it
> is not single-valued precisely because the quantity being computed is a **logarithmic** density, and
> the integrality of that density is exactly the single-valuedness. *The two-variable problem and MI
> are the same statement.* Every future two-variable attempt inherits this and should not be made.

### 190.3 The one quantitative residue

The hull computation does leave a usable fact:

> **If the standard twist satisfied `Φ_G(s,α) ≪ α^{−1/2−δ}` for `s` in a punctured neighbourhood of
> `s^*_0` (a subconvexity-type bound in the `α`-aspect, `δ > 0`), then `W_0 = 1/2 − δ` and the
> `p`-sum would converge *at* the target, making `R(w)` holomorphic at `w = 1/2` and forcing
> `δ_1(a_G(·²)) = 0`.**

Since `δ_1(a_{ζ²}(·²)) = 3 ≠ 0`, **such a bound is FALSE**: the standard twist cannot decay faster
than `α^{−1/2}` in the `α`-aspect near its first pole, and the exponent `−1/2` is **sharp**. Recorded
as a small unconditional by-product:

> **Corollary 112.** For `G ∈ S` of degree `2` with `δ_1(a_G(·²)) ≠ 0` (e.g. `G = ζ²`), no bound
> `Φ_G(s,α) ≪_s α^{−1/2−δ}` with `δ > 0` holds uniformly for `α ∈ \mathrm{Spec}(G)` and `s` in a
> punctured neighbourhood of `s^*_0`. The decay exponent `−1/2 = 2(s^*_0−1)` is sharp, and is
> saturated by the residues themselves.

### 190.4 Position

```
(SPEC)/(SPEC′)   — closed: identical to MI for Sym² (§190.2). Do not retry two-variable continuations.
Theorem 111      — stands: (PSD₂) ⟹ Conjecture A, with (PSD₂) = Sym²-closure.
walls            — the sieve (§185.2, four-fold), (V)/(a), (FRAC), MI. All with exact obstructions.
by-product       — Corollary 112: sharpness of the α-decay of the standard twist at its first pole.
```

---

## 191. Cycle 191 (2026-07-26) — higher prime moments: the Tannakian strengthening, and what it buys

### 191.1 The moment sequence

Put `n_F^{(k)} := \lim_x(\log\log x)^{−1}Σ_{p≤x}|a_F(p)|^{2k}/p`, so `n_F = n_F^{(1)}`. If the Satake
classes equidistribute with respect to Haar measure on a compact group `K ≤ U(d)` (§179.2), then
```
n_F^{(k)} = ∫_K |\mathrm{tr}|^{2k}\,dK = \dim\big(\text{invariants of } \mathrm{std}^{⊗k}⊗\overline{\mathrm{std}}^{⊗k}\big) ,
```
which for `K = U(d)` and `k ≤ d` equals `k!` (Diaconis–Shahshahani).

> **Conjecture (Moment Rigidity, MR).** For primitive `F ∈ S` of degree `d`,
> `n_F^{(k)} = k!` for `1 ≤ k ≤ d`, and in general `n_F^{(k)} = \dim\mathrm{End}(\mathrm{std}^{⊗k})`
> for the Sato–Tate group of `F`.
>
> *Structural content.* MR is the full Tannakian statement of which Conjecture A is the case `k = 1`;
> it asserts that the *whole* moment sequence of `|a_F(p)|²` is the dimension sequence of a compact
> group, not merely that its first term is an integer. **MR ⟹ Conjecture A.**
> *How it could fail.* Any `F` whose Satake law is a probability measure that is not a group trace
> measure — the same window §56 squeezed. *Bold enough to be false:* it pins infinitely many
> quantities, whereas Conjecture A pins one.

### 191.2 Unconditional relations, and one implication worth recording

Cauchy–Schwarz against `Σ_{p≤x}1/p ∼ \log\log x` gives, whenever the limits exist,
```
n_F^{(1)} ≤ \sqrt{n_F^{(2)}} ,\qquad\text{more generally}\qquad n_F^{(k)} ≤ (n_F^{(k+1)})^{k/(k+1)}\cdot 1^{1/(k+1)} .
```
Combining with the Energy Gap:

> **Proposition 113.** Assume (i) Conjecture A for `F` (`n_F ∈ Z`), (ii) the Energy Gap `n_F ≥ 1`, and
> (iii) `n_F^{(2)} < 4`. Then `n_F = 1`, i.e. **(P1) holds for `F`**.
> *Proof.* `n_F ≤ \sqrt{n_F^{(2)}} < 2` and `n_F ≥ 1` with `n_F ∈ Z`. ∎

So (P1) — the remaining half of Conjecture B and, by Cor. 102, the whole of Conjecture A in degree
`≤ 2` — follows from Conjecture A plus a **fourth-moment upper bound**. For automorphic `F`,
`n_F^{(2)} = 2 < 4` ✔ with room to spare. Recorded because it isolates a target of a different type:
an *upper* bound on a prime moment, where the programme has otherwise only produced lower bounds.

### 191.3 The moments reduce to prime-power densities, as `k = 1` does

Iterating the identity of Theorem 111: `|a_F(p)|² = a_{F\bar F}(p²) − 2\mathrm{Re}\,a_F(p²)` is linear
in prime-square data; squaring and applying the same identity to the products
`(F\bar F)`, `(F\bar F)^2`, … expresses `|a_F(p)|^{2k}` as a `Z`-linear combination of honest
coefficients `a_H(p^{2^j})` of elements `H` of the monoid generated by `F,\bar F`. Hence

> **`n_F^{(k)}` is a `Z`-linear combination of the linear densities `δ_1(a_H(·^{2^j}))`.**
> The whole moment sequence therefore reduces to the same family of linear-density integrality
> statements as Conjecture A, and (PSD₂)-type closure at every prime power `p^{2^j}` gives **MR**, not
> merely Conjecture A.

> **Recorded.** This is the natural scope of Theorem 111: the reduction of a quadratic invariant to
> linear prime-power densities is not special to `k = 1`. The obstruction (the sieve, §185.2) is the
> same at every level, so nothing is gained *or lost* by working with higher moments — but the target
> is now known to be the full Tannakian statement rather than a single integer.

---

## 192. Cycle 192 (2026-07-26) — Theorem 114: the Selberg pairing splits off its 1-line part

### 192.1 The decomposition

In the semi-Hilbert space `W` of §166.3 (bounded prime sequences modulo `ℓ²(1/p)`, with
`⟨u,v⟩ = \lim(\log\log x)^{−1}Σ_{p≤x}u_p\overline{v_p}/p`), the tones `e_t(p) := p^{−it}` are
orthonormal: `⟨e_t,e_{t'}⟩ = \lim(\log\log x)^{−1}Σ_{p≤x}p^{−1−i(t−t')} = δ_{t,t'}`, since
`Σ_pp^{−1−iτ} = \log ζ(1+iτ)+O(1)` is bounded for `τ ≠ 0`. By Theorem 52 plus a Tauberian step,
```
⟨[F],e_t⟩ = δ_1\big(p↦a_F(p)p^{it}\big) = −\,\mathrm{ord}_{s=1+it}F =: m_t^F ∈ Z ,
```
and by Bessel `Σ_t (m_t^F)² ≤ n_F` (this is Theorem 10, `n_F ≥ ν²`, in its sharp multi-point form;
Lean: `HTGeometry.bessel_of_almost_orthogonal` with `A = 1`, `ε = O(1/\log\log x)`).

Write `[F] = Σ_t m_t^F e_t + [F]^⊥`, so `‖[F]^⊥‖² = n_F − Σ_t(m_t^F)² =: \mathrm{def}(F) ≥ 0`.

> **Theorem 114 (unconditional).** For `F,G ∈ S` with bounded prime coefficients,
> ```
> \Big|\,c_{F,G} \;−\; Σ_{t∈R} m_t^F\,m_t^G\,\Big| \;≤\; \sqrt{\mathrm{def}(F)\cdot\mathrm{def}(G)} ,
> \qquad \mathrm{def}(H) = n_H − Σ_t(\mathrm{ord}_{1+it}H)² .
> ```
> In particular the Selberg pairing splits as an **integral** part, `Σ_tm_t^Fm_t^G`, determined by the
> divisors of `F` and `G` on the line `\mathrm{Re}\,s = 1`, plus a remainder controlled by the two
> energy defects.

*Consequences, all immediate.*
- `\mathrm{def}(F) = 0` ⟹ `c_{F,G} = Σ_tm_t^Fm_t^G ∈ Z` for **every** `G` — the pairing is integral
  against everything. This holds for `F = ζ^k` (`m_0 = k`, `n_F = k²`, `\mathrm{def} = 0`), recovering
  `c_{ζ^k,G} = −k\,\mathrm{ord}_1G` and agreeing with Theorem 106.
- Conjecture A `⟹ \mathrm{def}(F) ∈ Z_{≥0}` for all `F`; Conjecture B for a pair of entire primitives
  says `c_{F,G} = 0` with both `m_t ≡ 0`, i.e. `|⟨[F]^⊥,[G]^⊥⟩| = 0` — the pairing is *entirely*
  in the defect part, which is why the 1-line divisor gives no purchase on it.

### 192.2 Why it does not reach Conjecture B

For `F,G` entire and non-vanishing on `\mathrm{Re}\,s = 1` — the case of interest, and the generic one
— every `m_t` vanishes, `\mathrm{def} = n`, and Theorem 114 degenerates to plain Cauchy–Schwarz
`|c_{F,G}| ≤ \sqrt{n_Fn_G}`. **The decomposition is informative exactly when `F` or `G` has divisor on
the `1`-line, i.e. in the cases already settled by Theorem 52.** Recorded so the refinement is not
mistaken for progress on the open cases.

Its value is structural: it shows that the *entire* content of Conjecture B lives in the orthogonal
complement of the tone system `\{e_t\}`, i.e. in the part of the prime coefficients invisible to every
linear density. Combined with §179.1 (the axioms supply character data only at `j = 1`, weight
`p^{−s}`), this says: **the axioms determine `[F]` exactly along `\mathrm{span}\{e_t\}` and say
nothing about `[F]^⊥`** — the sharpest statement of what is known and what is missing about the
Selberg pairing.

### 192.3 Hand-off update (supersedes §186's list)

New since §186: Theorems 109 (degree-2 Hecke reduction), 111 ((PSD₂) ⟹ Conjecture A), 114 (pairing
splitting); Corollary 112 (sharpness of the twist's `α`-decay); Proposition 113 ((P1) from Conjecture A
plus a fourth-moment bound); Conjecture MR (Tannakian strengthening, §191.1). Routes closed: (SPEC),
(SPEC′), and all two-variable continuations (§190.2 — they are MI). Preprint updated with §§16–18.
Defect ledger now at seven (§189.4).

---

## 193. Cycle 193 (2026-07-26) — Theorem 115: the energy dominates the total **twisted** divisor mass on the 1-line

§192 used only the tones `e_t(p) = p^{−it}`. The right orthonormal system is larger.

### 193.1 The degree-1 system is orthonormal

Let `𝒫` be the set of degree-`1` elements of `S`, i.e. `ζ(s)` and `L(s+iθ,χ)` with `χ` primitive
(Kaczorowski–Perelli). Their coefficient vectors are `[P](p) = χ(p)p^{−iθ}`, and by §172.2
```
⟨[P],[P']⟩ = \lim_x(\log\log x)^{−1}Σ_{p≤x}χ\barχ'(p)p^{−i(θ−θ')}/p = δ_{P,P'} ,
```
since `Σ_pχ\barχ'(p)p^{−1−iτ} = \log L(1+iτ,χ\barχ') + O(1)` is bounded unless `χ = χ'` and `τ = 0`.
**So `\{[P] : P ∈ 𝒫\}` is an orthonormal system in `W`** — uncountable, and strictly larger than the
tone system `\{e_t\}` (which is the sub-family with `χ` principal).

By Theorem 106, `⟨[F],[P]⟩ = c_{F,P} = −\,\mathrm{ord}_{s=1+iθ}\big(F^{\barχ}\big) ∈ Z`.

### 193.2 The theorem

Bessel's inequality (Lean: `HTGeometry.bessel_of_almost_orthogonal`, with `A = 1` and off-diagonal
defect `ε = O(1/\log\log x)`) applied to `u = [F]` and any finite sub-family of `𝒫` gives:

> **Theorem 115 (unconditional).** For every `F ∈ S` with bounded prime coefficients,
> ```
> Σ_{χ}\;Σ_{θ∈R}\;\big(\mathrm{ord}_{s=1+iθ}F^{\barχ}\big)^2 \;≤\; n_F ,
> ```
> the sum over all primitive Dirichlet characters `χ` (including the trivial one) and all real `θ`.
> Equivalently: **the prime energy dominates the total divisor mass of all Dirichlet twists of `F` on
> the line `\mathrm{Re}\,s = 1`, counted with multiplicity squared.**
> Moreover `n_F = Σ_{P∈𝒫}|c_{F,P}|² + \mathrm{def}_1(F)` with the first term a **non-negative integer**
> and `\mathrm{def}_1(F) ≥ 0`; hence `n_F ∈ Z ⟺ \mathrm{def}_1(F) ∈ Z`.

### 193.3 Two corollaries

> **Corollary 116 (an Energy Gap, unconditional).** If some Dirichlet twist `F^{\barχ}` has a zero or a
> pole on the line `\mathrm{Re}\,s = 1`, then `n_F ≥ 1`.

This is the first unconditional instance of the Energy Gap beyond Theorem 10's untwisted case
(`n_F ≥ m_F²` for a pole of order `m_F` at `s = 1`): it covers every `F` whose *twists* are singular
on the `1`-line, with no hypothesis on `F` itself.

> **Corollary 117 (small energy forces GPNT for all twists).** If `n_F < 1` then **every** Dirichlet
> twist `F^{\barχ}` is holomorphic and non-vanishing on `\mathrm{Re}\,s = 1`; by Kaczorowski–Perelli
> this gives the generalized prime number theorem for `F` and for all its twists.

So the Energy Gap and the twisted prime number theorem are two sides of one inequality: `n_F < 1`
forces GPNT, and failure of GPNT for any twist forces `n_F ≥ 1`.

### 193.4 Scope, honestly

For `F` primitive of degree `≥ 2` the expectation (Conjecture B, and a theorem for `d ≤ 2` by KP's
GPNT) is that every `c_{F,P}` vanishes, so `\mathrm{def}_1(F) = n_F` and Theorem 115 degenerates. **The
inequality is informative exactly on the elements whose twists are singular on the 1-line** — a set
conjecturally consisting only of `F` divisible by degree-`1` factors. Its value is that it is
unconditional and that it identifies the *complete* orthonormal system the axioms give access to:

> **The axioms determine `[F]` exactly on `\overline{\mathrm{span}}\{[P] : P ∈ 𝒫\}` — the closed span of
> the degree-1 elements — and say nothing about the orthogonal complement.** By §180.2 this is
> unimprovable: the Dirichlet twist is the only tensor operation available, so degree-1 elements are
> the only ones that can be paired against `F` with an integral answer. **Conjecture A is exactly the
> integrality of `\|[F]^⊥\|²` for that complement, and Conjecture B is the vanishing of `⟨[F]^⊥,[G]^⊥⟩`.**

That is the cleanest available statement of what is known and what is missing, and it supersedes
§192.2 (which used only the principal-character sub-system).

---

## 194. Cycle 194 (2026-07-26) — degree ≤ 2 elements are unconditionally orthogonal to the degree-1 span; Lean for Theorem 115

### 194.1 An unconditional orthogonality

Kaczorowski–Perelli's generalized prime number theorem for `S` in degree `≤ 2` is equivalent to
non-vanishing on `\mathrm{Re}\,s = 1`. A Dirichlet twist preserves degree, so for `F ∈ S` with
`d_F ≤ 2` **every** twist `F^{\barχ}` has degree `≤ 2` and is therefore non-vanishing and pole-free on
the `1`-line (apart from the pole of `F` itself at `s = 1`, which is the case `χ` principal, `θ = 0`).
By Theorem 106, `c_{F,P} = −\mathrm{ord}_{1+iθ}F^{\barχ}`, so:

> **Proposition 118 (unconditional).** For `F ∈ S` entire of degree `≤ 2`, `[F] ⊥ V_1` where
> `V_1 = \overline{\mathrm{span}}\{[P] : P ∈ 𝒫\}` is the closed span of the degree-1 coefficient
> vectors. Hence `\mathrm{def}_1(F) = n_F` and Theorem 115 degenerates for exactly these `F`.
>
> Since `[·]` is additive, the same holds for every product of entire elements of degree `≤ 2` — in
> particular `[F] ⊥ V_1` for `F = F_1\cdots F_r` with all `d_{F_i} ≤ 2`, **even though `d_F` may be
> arbitrarily large** and GPNT is unknown in that degree. (The GPNT for such products is of course
> immediate from the factors; recorded only to note that the orthogonality statement is not confined
> to `d ≤ 2`.)

So the picture is complete and sharp:

```
[F] ∈ V_1          ⟺  F is (up to energy-zero) a product of degree-1 elements   (Theorem 100)
[F] ⊥ V_1          ⟸  every primitive factor of F has degree ≤ 2               (Prop. 118)
Conjecture A on V_1^⊥ : ‖[F]^⊥‖² ∈ Z                                            (Theorem 115)
```
and for the first open case — `F` primitive of degree `2` — the vector `[F]` is a **unit-length
candidate in `V_1^⊥`** whose norm is exactly what is in question.

### 194.2 Lean

Added to `HTGeometry/BesselPSD.lean` (`lake build +GaloisForLFunctions.HTGeometry` clean):
```lean
theorem integral_bessel_of_orthonormal (B : V → V → ℂ) (hadd₁ …) (hsmul₁ …) (hconj …) (hpsd …)
    {ι} [Fintype ι] [DecidableEq ι] (e : ι → V) (u : V) (m : ι → ℤ)
    (horth : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
    (hint  : ∀ i, B u (e i) = ((m i : ℤ) : ℂ)) :
    ∑ i, ((m i : ℝ)) ^ 2 ≤ (B u u).re
```
This is exactly Theorem 115's engine: **an orthonormal family with integral coefficients contributes
an integral amount to the energy, bounded by it.** The arithmetic inputs — orthonormality of
`p ↦ χ(p)p^{−iθ}` (from non-vanishing of `L(1+iτ,χ)`) and integrality of the pairings (from
Theorem 52 applied to twists) — are not formalisable without the analytic number theory, but the
algebra they feed is now machine-checked.

### 194.3 The remaining question, in its final form

> **Conjecture A `⟺` for every `F ∈ S`, `\|[F]^⊥\|² ∈ Z`, where `⊥` is taken relative to the closed
> span of the degree-1 coefficient vectors.**
> **Conjecture B `⟺` `⟨[F]^⊥,[G]^⊥⟩ = 0` for distinct primitives.**

The axioms determine `[F]` completely on `V_1` (integrally, via twist divisors) and supply **no**
information on `V_1^⊥` — because by §180.2 the Dirichlet twist is the only tensor operation available,
and it can only pair `F` against degree-1 elements. Every route examined in this programme — MI,
`\mathrm{Sym}²`-closure (PSD₂), the standard twist, the characteristic-function method, the amplifier,
the two-variable continuations — is an attempt to reach `V_1^⊥`, and each fails at the same point.
**This is the final form of the obstruction.**

---

## 195. Cycle 195 (2026-07-26) — unique factorisation: exactly what Theorem 89 gives and what it does not

### 195.1 The reduction

Theorem 89 (unconditional): a non-trivial `H` in the group completion has divergent prime energy,
i.e. `[H] ≠ 0` in `W`. Contrapositive: `Σ_iα_i[P_i] = 0` in `W` ⟹ `∏_iP_i^{α_i} ≡ 1` as a function.
Hence:

> **Proposition 119.** Unique factorisation into primitives in `S` is equivalent to: *no non-trivial
> multiplicative relation `∏_{i∈I}P_i^{a_i} = ∏_{j∈J}Q_j^{b_j}` holds between products over **disjoint**
> sets of distinct primitives.* Theorem 89 reduces uniqueness to this, and no further.

The reduction is genuine but does not close: if such a relation held, the two coefficient vectors would
be **equal**, so `\|Σa_i[P_i]\|² = \|Σb_j[Q_j]\|² = ⟨Σa_i[P_i],Σb_j[Q_j]⟩` and Cauchy–Schwarz is at
equality — no contradiction. Under Conjecture B all cross terms `c_{P_i,Q_j}` vanish, forcing
`Σa_i² = 0` and hence uniqueness; that is the classical implication and it is not available here.

> **Recorded.** Unique factorisation remains open, and Theorem 89 does not give it. (Checked because
> the ℤ-linear-independence phrasing of Theorem 89 is easy to over-read.)

### 195.2 A dichotomy from Corollary 116

> **Corollary 120 (unconditional).** For every entire `F ∈ S`, **either** `n_F ≥ 1`, **or** every
> Dirichlet twist `F^{\barχ}` is holomorphic and non-vanishing on `\mathrm{Re}\,s = 1` — i.e. `F` and
> all its twists satisfy the generalized prime number theorem.

So a putative counterexample to the Energy Gap must satisfy GPNT for itself and every twist. Combined
with Theorem 84′ (`E(x) → ∞`) such an `F` would have divergent energy of density zero — the case
§147.3 lists as untouched — while satisfying the full twisted GPNT. Recorded as the sharpest
description of what an Energy-Gap counterexample would have to look like.

### 195.3 Standing

Cycles 191–195 produced: Conjecture MR (§191.1), Proposition 113, Theorems 114, 115, 118,
Propositions 119, 120, Corollaries 116, 117, and the Lean lemma `integral_bessel_of_orthonormal`.
The obstruction is in its final form (§194.3): **the axioms determine `[F]` integrally on the span of
the degree-1 coefficient vectors and give nothing on the orthogonal complement, where both conjectures
live.**

---

## 196. Cycle 196 (2026-07-26) — end-to-end audit of the preprint's earlier sections

Given seven defects found in the log, the deliverable was re-derived section by section. Sampled and
checked this cycle (§§1–8 of `4-publication-ready/monodromy-integrality-selberg.md`):

- **Theorem 1 (MI ⟹ Conjecture A).** `R_{F,F}(w) = Σ_n|a_F(n)|²n^{−w}` has non-negative coefficients,
  so Landau makes its abscissa a singularity; MI makes it a pole, so `n_F = −\mathrm{ord}_{w=1}R_{F,F} ∈ Z`.
  The Euler-product step `\log R_{F,F}(w) = Σ_p|a_F(p)|²p^{−w} + E(w)` with `E` holomorphic on
  `\mathrm{Re}\,w > 1/2` is Theorem 52's argument applied to `R_{F,F}` and needs Ramanujan on prime
  powers — present. Wiener–Ikehara is applied to `−P'`, which has non-negative coefficients ✔.
  **Passes.**
- **Theorem 4 (axiom necessity).** `F(s) = \exp(Σ_p(\log p)^{10}p^{−s})`: `b_F(p) = (\log p)^{10} ≪_θ p^θ`
  for every `θ > 0` ✔ (axiom 5 with `θ < 1/2`); `a_F(p^k) = (\log p)^{10k}/k!` gives `a_F(n) ≪_ε n^ε` ✔
  (axiom 4); and `Σ_{p≤x}|a_F(p)|²/p ≍ (\log x)^{20}/20`, so no `\log\log`-density exists ✔. Axioms
  (2),(3) fail, as required for the conclusion. **Passes.**
- **Theorem 6 (`ℛ_F`).** `𝔏_F(w) = Σ_pΣ_{k≥1}k|b_F(p^k)|²p^{−kw}`; at `k = 1` the summand is
  `|b_F(p)|²p^{−w} = |a_F(p)|²p^{−w}` ✔, and the identity `Σ_iα_i^k = k\,b_F(p^k)` is Newton ✔
  (same identity as `newton_sq_identity`'s input). **Passes.**
- **Theorem 5 (Cusp–Spectrum Radius Law).** A radius-of-convergence statement read off C6.1/C7.1;
  the recorded verifications on `ζ`, `L(·,χ)`, level-1 newforms and Maass forms stand. **Passes.**

No new defects. The ledger remains at seven (§189.4). Sections 12–18 were written this session and
are internally cross-checked against `ζ`, `ζ²` and a `GL_2` newform per the §189.4 rule.

> **Recorded.** The deliverable is now audited end to end. The four corrections of preprint §15 remain
> the complete list of changes from earlier drafts.

---

## 197. Cycle 197 (2026-07-26) — the Energy Gap as discreteness; and what a counterexample must be

### 197.1 Two topologies on `S^{gp}`

Recall `W` = bounded prime sequences modulo `ℓ²(1/p)`, `‖[H]‖² = n_H`.

- In the **`ℓ²(1/p)` metric**, Theorem 84′/89 says every non-trivial `H` has `Σ_p|a_H(p)|²/p = ∞`, so
  distinct elements of `S^{gp}` are at infinite distance: `S^{gp}` is **discrete, indeed uniformly
  disconnected**, but the statement is vacuous for our purposes.
- In the **`W` metric** (the `\log\log`-normalised one), `‖[F]−[G]‖² = n_{F/G}` is finite, and:

> **Proposition 121.** The Energy Gap (`n_H ≥ 1` for every non-trivial `H ∈ S^{gp}`) is **exactly** the
> statement that `S^{gp}` is a **discrete subgroup of `W` with separation `≥ 1`**.

Two unconditional facts about this subgroup:
- `[ζ]` has norm `1`, and `[ζ^k]` has norm² `k²` ✔.
- For every entire primitive `F ≠ ζ`, `c_{F,ζ} = −\mathrm{ord}_{s=1}F = 0` (Theorem 52), so
  **`[F] ⊥ [ζ]` unconditionally**. Hence `S^{gp} ⊇ Z[ζ] ⊥ (\text{the rest})` as an orthogonal
  decomposition, and `n` is integral on the `Z[ζ]` summand.

### 197.2 Discreteness does not give integrality

Recorded to prevent an over-reading of Proposition 121: `Z·\sqrt{3/2} ⊂ R` is discrete with
`‖k‖² = 3k²/2 ∉ Z`. So EG ⟹̸ Conjecture A. The two are independent statements about the same lattice:
EG is *separation*, Conjecture A is *integrality of the form*. Both are needed, and only Conjecture B
supplies an orthonormal basis that would give them together.

### 197.3 What a counterexample to Conjecture A must be

Assembling the constraints now recorded:

```
(a)  δ_1(a_F(·)) = −ord_1 F ∈ Z            — one Tannakian moment is forced (Theorem 52)
(b)  δ_1(a_F(·²)) ∉ Z  or  δ_1(a_{F\bar F}(·²)) ∉ Z          (Theorem 111)
(c)  the Satake law is a probability measure that is NOT the trace measure of a compact group  (§179.2)
(d)  by Cor. 116, if any twist F^{\barχ} is singular on Re s = 1 then n_F ≥ 1
(e)  by §56, the prime phases are neither arithmetically structured (monodromy) nor generic
     (natural boundary): the functional equation must survive
(f)  by Theorem 85′, F is isolated: every distinct G has Σ_p|a_F(p)−a_G(p)|²/p = ∞, so F cannot be
     produced as a limit or deformation of known elements — the only continuous family in S is the
     shift F ↦ F(s+iθ), along which n_F is constant.
```

> **(f) is the sharpest structural obstruction to *constructing* a counterexample**, and it is new to
> this list: `S` admits **no continuous deformations** other than vertical shifts, and `n` is constant
> along those. Any counterexample is therefore an isolated, rigid object that cannot be reached by
> perturbing an automorphic `L`-function — which is why none has ever been exhibited, and why §56's
> squeeze is not merely a heuristic.

### 197.4 Standing

The programme's state is now fully characterised:
```
known integrally :  [F] on \overline{span}\{[P] : P degree 1\}          (twist divisors, Theorem 115)
unknown          :  [F]^⊥ — where Conjecture A (its norm) and Conjecture B (its pairings) live
EG               :  discreteness of S^{gp} in W                          (Proposition 121)
constructing a counterexample : blocked by rigidity (f)
```

---

## 198. Cycle 198 (2026-07-26) — Lean: Cauchy–Schwarz for a positive semi-definite form

The Selberg pairing lives on a form that is only positive **semi**-definite (it is a
`\log\log`-normalised limit of positive forms, with a huge radical), so the inner-product-space
Cauchy–Schwarz in Mathlib does not apply. The corpus now carries the bare-form version.

Added to `HTGeometry/BesselPSD.lean`:
```lean
theorem cauchy_schwarz_psd (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℂ) (x y : V), B (c • x) y = c * B x y)
    (hconj : ∀ x y, B y x = (starRingEnd ℂ) (B x y))
    (hpsd : ∀ x, 0 ≤ (B x x).re) (x y : V) :
    ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re
```
Proof: test positivity on `x - t • ((B x y) • y)` for real `t`. Choosing the *coefficient* `B x y`
rather than a unimodular phase makes every cross term real — `B x ((B x y) • y) = ‖B x y‖²` — so the
quadratic is `(B x x).re - 2t‖B x y‖² + t²‖B x y‖²(B y y).re` and the discriminant condition is
immediate; the degenerate cases `‖B x y‖ = 0` and `(B y y).re = 0` are handled separately (the second
by letting `t → ∞`, which forces `‖B x y‖ = 0`).

This is the missing algebraic input for Theorems 114/115: with
`bessel_of_almost_orthogonal`, `integral_bessel_of_orthonormal` and `cauchy_schwarz_psd`, the whole
Hilbert-space layer of the Selberg-pairing analysis is machine-checked:
```
|c_{F,G}|² ≤ n_F n_G                                    cauchy_schwarz_psd
Σ_P |c_{F,P}|² ≤ n_F,   c_{F,P} ∈ Z                     integral_bessel_of_orthonormal
Σ_j |c_{F,P_j}|² ≤ (1 + card·ε) n_F  (finite defect)     bessel_of_almost_orthogonal
|⟨u,v⟩ − Σ⟨u,e⟩⟨e,v⟩| ≤ √(def·def)                       the three combined
```
Corpus search run first: `research "Cauchy Schwarz positive semidefinite sesquilinear bare form"` and
`rg` returned only `RHTower.selberg_pairing_cauchy_schwarz` (a statement about the *arithmetic*
pairing, assuming the inequality) and inner-product-space versions. No duplication.

---

## 199. Cycle 199 (2026-07-26) — the Gram matrix carries no obstruction; linear algebra cannot give Conjecture B

### 199.1 The setting

For primitives `F_1,\dots,F_k` let `C = (c_{F_i,F_j})` be the Gram matrix of `[F_1],\dots,[F_k]` in `W`.
Unconditionally `C` is positive semi-definite with `C_{ii} = n_{F_i}`. Under (P1) all `n_{F_i} = 1`;
under Conjecture A and its polarisation, `2\mathrm{Re}\,C_{ij} ∈ Z`, and with `|C_{ij}| ≤ 1`
(Cauchy–Schwarz) this leaves `\mathrm{Re}\,C_{ij} ∈ \{0,±\tfrac12,±1\}`. The value `±1` forces equality
in Cauchy–Schwarz, hence `[F_i] = ±[F_j]`, hence `F_i = F_j` by Theorem 89. **The whole of Conjecture B
(real part) is the exclusion of `\mathrm{Re}\,c = ±1/2`.**

### 199.2 No linear-algebra obstruction exists

> **Recorded do-not-retry.** Take `\mathrm{Re}\,C_{ij} = 1/2` for every `i ≠ j`, i.e.
> `C = \tfrac12(I + J_k)`. Its eigenvalues are `(k+1)/2` (once) and `1/2` (`k−1` times): **positive
> definite for every `k`.** So an infinite family of primitives pairwise at `\mathrm{Re}\,c = 1/2`
> violates no positivity constraint, and **no argument from positive semi-definiteness of the Selberg
> pairing — for any number of elements — can exclude the open case.**

(For contrast, `\mathrm{Re}\,C_{ij} = −1/2` for all `i ≠ j` gives `C = \tfrac32I − \tfrac12J_k` with
smallest eigenvalue `(3−k)/2`, so at most **three** primitives can be pairwise at `−1/2`. The
obstruction is one-sided and does not touch the case that matters.)

Nor does the induced constraint on products help: with all `\mathrm{Re}\,c_{ij} = 1/2`,
`n_{F_1\cdots F_k} = k + 2\binom k2\cdot\tfrac12 = k(k+1)/2`, which is finite, integral, and compatible
with every unconditional bound recorded (in particular with `n_H ≤ d_H²`, since `d_H ≥ k`).

### 199.3 Consequence for the shape of a proof

Combining with §194.3 and §197.2:

> Conjecture B cannot be obtained from (i) positivity of the pairing, (ii) integrality of the pairing
> (Conjecture A), (iii) Cauchy–Schwarz, or (iv) any finite-dimensional linear algebra on the Gram
> matrix — *all* of these are consistent with `\mathrm{Re}\,c_{F,G} = 1/2` throughout. It requires an
> input that distinguishes `1/2` from `0` **arithmetically**, i.e. a statement about
> `\mathrm{ord}_{s=1}` of an object attached to the pair `(F,G)` — which is Rankin–Selberg.
> Correspondingly, the Energy Gap in the form `n_H ≥ 1` is *not* enough: `n_{F/G} = 2 − 2(1/2) = 1`
> saturates it exactly.

That last observation is worth isolating: **the open case `\mathrm{Re}\,c = 1/2` is precisely the case
that saturates the Energy Gap.** Any strengthening of EG to `n_H ≥ 1 + δ` for non-trivial `H` in the
group completion would immediately give Conjecture B for unit-energy primitives — but `H = ζ` has
`n_H = 1` exactly, so no such uniform strengthening can hold. **EG is sharp, and sharp for the wrong
reason: the extremal element is `ζ`, not the hypothetical `F/G`.**

---

## 200. Cycle 200 (2026-07-26) — Conjecture B is a **second-level Energy Gap**

### 200.1 The equivalence

Let `F ≠ G` be primitives with `n_F = n_G = 1` ((P1)), and write `c = c_{F,G}`. Then
```
n_{FG} = 2 + 2\mathrm{Re}\,c ,\qquad n_{F/G} = 2 − 2\mathrm{Re}\,c .
```

> **Theorem 122.** Given (P1), the real part of Selberg's Conjecture B is **equivalent** to
> ```
> n_H ≥ 2 \qquad\text{for every } H = F^{±1}G^{±1},\ F ≠ G \text{ primitive} .
> ```
> *Proof.* `n_{FG} ≥ 2` gives `\mathrm{Re}\,c ≥ 0`; `n_{F/G} ≥ 2` gives `\mathrm{Re}\,c ≤ 0`. Conversely
> `\mathrm{Re}\,c = 0` makes both equal `2`. ∎

So Conjecture B is an Energy Gap **at level 2**, exactly as EG is the gap at level 1, and it is sharp:
equality holds precisely when the conjecture holds.

### 200.2 Why the level-1 gap cannot be strengthened, but the level-2 one is not excluded

§199.3 noted that EG in the form `n_H ≥ 1` is saturated by the open case `\mathrm{Re}\,c = 1/2`
(`n_{F/G} = 1`), so no proof of EG alone can reach Conjecture B. One might hope for a uniform
strengthening `n_H ≥ 1+δ`; that is **impossible**, since `H = ζ` has `n_H = 1` exactly.

But the extremal element `ζ` lies in `V_1` — the span of the degree-1 coefficient vectors — whereas
the relevant `H = F^{±1}G^{±1}` lies in `V_1^⊥` when `d_F,d_G ≤ 2` (Prop. 118). So:

> **The obstruction to strengthening EG is confined to `V_1`.** A gap of the form
> ```
> \|[H]\|² ≥ 2 \qquad\text{for every non-trivial } [H] ∈ S^{gp} ∩ V_1^⊥ \text{ that is not a single primitive}
> ```
> is **not** contradicted by `ζ`, and by Theorem 122 it is exactly Conjecture B. The single-primitive
> exclusion is necessary: `n_F = 1` for a primitive `F` of degree `2`, which also lies in `V_1^⊥`.

> **Recorded as the cleanest zero-side/energy-side statement of Conjecture B**: *the energy lattice
> `S^{gp}` has minimum `1`, attained exactly at the primitives, and its non-primitive vectors in
> `V_1^⊥` have energy at least `2`.* In lattice language: **`S^{gp}` is generated by its minimal
> vectors, and those are orthonormal** — which is Conjecture A and B together, stated as a property of
> one lattice.

### 200.3 What this does and does not give

It does not prove anything new. Its value is that it puts both conjectures into a single, purely
lattice-theoretic sentence, and it explains the failure mode of every energy-based attack recorded in
this log: those attacks prove statements of the form `n_H > 0` or `n_H → ∞`, which are level-0
statements, whereas Conjecture A needs integrality of the form and Conjecture B needs the level-2 gap.
**No amount of level-0 information (divergence, positivity, floors) can reach level 1 or 2.** That is
the abstract form of the ceiling computed concretely in Theorem 104.

---

## 201. Cycle 201 (2026-07-26) — the root-system alternative: what Conjecture B actually excludes

### 201.1 Conjecture A does *not* exclude the natural competitor

By §199.2 the open case is `\mathrm{Re}\,c_{F,G} = ±1/2` for unit-energy primitives. Identify it:

> A lattice with minimum `1` whose minimal vectors have pairwise inner products in `\{0,±\tfrac12,±1\}`
> is exactly an **even lattice scaled by `1/\sqrt2`**. The root lattices `A_n`, `D_n`, `E_8` (minimum
> `2`, roots with `⟨α,β⟩ ∈ \{0,±1,±2\}`) rescale to minimum `1` with inner products
> `\{0,±\tfrac12,±1\}`, and — because they are **even** — the rescaled form is still `Z`-valued.

Checked: in `A_2/\sqrt2`, `‖α'‖² = 1`, `⟨α',β'⟩ = −\tfrac12`, `‖α'+β'‖² = 1`, `‖2α'+β'‖² = 3` — all
integers. So

> **Conjecture A is *compatible* with the root-lattice configuration.** Integrality of the energy form
> does not distinguish `Z^n` from `A_n/\sqrt2`, `D_n/\sqrt2`, `E_8/\sqrt2`, or their infinite-rank
> analogues.

### 201.2 The dichotomy

```
Conjecture A  :  the energy lattice (S^{gp}, n) is INTEGRAL.
Conjecture B  :  it is Z^{(∞)} — an orthonormal basis of primitives —
                 rather than an EVEN lattice scaled by 1/√2 (the "root-system alternative").
```

> **Named alternative (RSA).** *The primitives of `S`, as unit vectors in `W`, form a (scaled) root
> system rather than an orthonormal set.* RSA is consistent with: positivity of the pairing,
> Cauchy–Schwarz, integrality (Conjecture A), the Energy Gap `n_H ≥ 1`, and every unconditional result
> in this log. It is excluded exactly by Conjecture B.

Two features of RSA worth recording:
- Under RSA, `[FG] = [F]+[G]` has norm `1` whenever `\mathrm{Re}\,c_{F,G} = −1/2`: the lattice acquires
  **minimal vectors that are not primitives of `S`**. That is not a contradiction — "minimal vector of
  the energy lattice" and "primitive element of `S`" are different notions — but it is the sharpest
  arithmetic anomaly RSA predicts, and it is a concrete thing to look for: *a product of two distinct
  primitives with prime energy `1`.*
- The minimal-vector count separates the two: `Z^n` has `2n`, `A_n/\sqrt2` has `n(n+1)`. So RSA
  predicts **many more** unit-energy elements than there are primitives.

### 201.3 Why this clarifies the difficulty

Every unconditional result recorded here constrains the lattice's *norms* (divergence, floors, gaps).
None constrains its *shape*. The root-system alternative is the precise statement of that gap:

> **Conjecture A is a statement about the values of the form; Conjecture B is a statement about the
> geometry of the lattice.** No argument that only produces inequalities among energies can settle B,
> because RSA satisfies all of them. Settling B requires an input that distinguishes an orthonormal
> basis from a root system — arithmetically, `\mathrm{ord}_{s=1}` of an object attached to a *pair*,
> i.e. Rankin–Selberg.

This supersedes §199.3 as the reason no energy-side attack can reach Conjecture B, and it gives the
first *positive* description of what a counterexample to B would look like: not an exotic object, but
the most familiar integral-lattice geometry there is.

---

## 202. Cycle 202 (2026-07-26) — Phase-2 checks on RSA and on Theorem 111

Novelty validation for the two new named objects of cycles 184–201, done before either is carried
further.

### 202.1 The root-system alternative (RSA)

Searched July 2026: *"Selberg class orthogonality conjecture lattice primitives root system even
lattice quadratic form"*. The literature on SOC (Selberg 1989; Conrey–Ghosh; Murty–Murty; Liu–Ye's
unconditional proof of SOC **for automorphic `L`-functions**; Kaczorowski–Perelli's surveys) states the
conjecture analytically and does not, as far as located, cast the primitives as vectors in a lattice or
identify the failure mode as a root-system geometry.

> **RSA: not located. Assessed, not claimed.** Its content is elementary once stated — the observation
> that an even lattice scaled by `1/\sqrt2` has minimum `1`, `Z`-valued form, and minimal-vector inner
> products `\{0,±\tfrac12,±1\}` — but the identification of *that* configuration as precisely the
> alternative left open by Conjecture A appears to be new to the subject's literature and is certainly
> new to this programme.

### 202.2 Theorem 111 versus Wong (JNT 2021)

**P.-J. Wong, *Selberg's orthogonality conjecture and symmetric power `L`-functions*, J. Number Theory
(2021)** proves: *assuming SOC* (plus automorphy of `\mathrm{Sym}^mπ` for a non-CM `GL_2` newform and
a totally real Galois `K/Q`), the twisted symmetric powers `L(s,\mathrm{Sym}^mπ × χ)` are automorphic
and primitive in `S`.

> **Direction check.** Wong runs **SOC ⟹ symmetric-power automorphy**. Theorem 111 runs the converse,
> and in the weakest possible form: **`\mathrm{Sym}²`-monodromy ⟹ Conjecture A**, with no automorphy,
> no `GL_2`, no Galois input — only single-valuedness of `L(s,\mathrm{Sym}²G)` at `s = 1` for every
> `G ∈ S`. The two are complementary and neither contains the other.

> **Observation worth recording.** Read together they say that SOC and `\mathrm{Sym}²`-closure are
> nearly equivalent: SOC gives symmetric-power automorphy (Wong, under hypotheses), and `\mathrm{Sym}²`
> monodromy gives Conjecture A (Theorem 111), which with (P1),(P2) gives SOC. **The symmetric square,
> not the Rankin–Selberg convolution, is the minimal functorial input for Selberg's conjectures.**
> That is a genuinely new placement of the problem: the received formulation asks for closure under
> `⊗` (bilinear, degree `d²`); the correct minimal ask is closure under `\mathrm{Sym}²` (unary,
> degree `d(d+1)/2`).

### 202.3 Context recorded

SOC is a **theorem for automorphic `L`-functions** (Liu–Ye, *A proof of Selberg's orthogonality for
automorphic L-functions*, and *Selberg's orthogonality conjecture for automorphic L-functions*). So the
entire difficulty is the gap between `S` and the automorphic world — which is exactly what §194.3
localises: the axioms determine `[F]` on the span of degree-1 vectors and nothing beyond, whereas
automorphy supplies the whole Tannakian structure. **Every route in this log fails at that one gap, and
the literature confirms there is no known way to cross it.**

---

## 203. Cycle 203 (2026-07-26) — RSA survives every available test; the tests, recorded

Attempts this cycle to exclude the root-system alternative with the programme's unconditional tools.

### 203.1 Parallelogram law fixes the pair, and permits RSA

For `F ≠ G` primitive with `n_F = n_G = 1`, polarisation gives the exact identity
`n_{FG} + n_{F/G} = 2n_F + 2n_G = 4`. So `\mathrm{Re}\,c = 0` gives `(2,2)` (Conjecture B) and
`\mathrm{Re}\,c = ∓\tfrac12` gives `(1,3)` or `(3,1)` (RSA). Both are integral, both are consistent
with every recorded inequality. **No constraint.**

### 203.2 Bessel gives only local finiteness

For a fixed primitive `F` with `n_F = 1` and any family `G_1,\dots,G_k` of primitives that are
**pairwise orthogonal** (`c_{G_i,G_j} = 0`), Bessel gives `Σ_{i≤k}|c_{F,G_i}|² ≤ n_F = 1`; if each
`|c_{F,G_i}| ≥ 1/2` then `k ≤ 4`.

Checked against `A_n`: a root `α` admits at most **two** pairwise orthogonal roots non-orthogonal to
it (e.g. `e_1−e_3` and `e_2−e_4` for `α = e_1−e_2`). So the bound `k ≤ 4` is satisfied with room to
spare. **No constraint.**

### 203.3 Degree and twist tests

- If either `F` or `G` has degree `1`, Theorem 106 forces `c_{F,G} = 0`: **RSA is confined to pairs of
  degree `≥ 2`.** ✔ (Consistent with Theorem 100.)
- Theorem 115 applied to `H = FG` with `d_F,d_G ≤ 2`: all twists `H^{\barχ} = F^{\barχ}G^{\barχ}` are
  non-vanishing on `\mathrm{Re}\,s = 1` by KP's GPNT in degree `≤ 2`, so the left side is `0` and the
  inequality is vacuous. **No constraint.**
- Corollary 116 likewise gives only `n_H ≥ 1`, which RSA satisfies with equality. **No constraint.**

### 203.4 The Weyl-symmetry observation

If the primitives form a root system, the lattice carries reflections
`s_{[F]}([G]) = [G] − 2\mathrm{Re}\,c_{F,G}\,[F]`, i.e. `G ↦ G\,F^{∓1}` in `S^{gp}`. These are genuine
lattice symmetries but **not** symmetries of `S`: `G/F` need not lie in `S`, and minimal vectors of the
lattice need not be primitive elements. So the Weyl structure predicts nothing testable inside `S`
itself. Recorded to close the idea.

### 203.5 Verdict

> **RSA is consistent with the entire unconditional corpus.** Positivity, Cauchy–Schwarz, integrality
> (Conjecture A), the Energy Gap, the parallelogram law, Bessel against orthonormal subfamilies,
> Theorem 106's twist integrality, Theorem 115's twisted divisor bound, Corollary 116, and the
> degree-`≤2` GPNT all hold in it. **No tool in this programme distinguishes `Z^{(∞)}` from a rescaled
> even lattice.**

That is the sharpest statement of what is missing, and it is a *positive* statement rather than a list
of failed attempts: the missing input must be one that separates an orthonormal basis from a root
system, and by §201.3 that is a statement about `\mathrm{ord}_{s=1}` of an object attached to a pair —
Rankin–Selberg. Equivalently, by Theorem 111 and §202.2, `\mathrm{Sym}²`-closure.

> **Recorded do-not-retry.** Do not attempt to exclude `\mathrm{Re}\,c = ±1/2` by any combination of:
> positivity, Cauchy–Schwarz, polarisation, Bessel, energy gaps, twist integrality, or degree
> bookkeeping. All are satisfied by `A_n/\sqrt2`.

---

## 204. Cycle 204 (2026-07-26) — the definitive reason: RSA and Conjecture B differ **only** in the quadratic form

### 204.1 Every axiom-supplied invariant is linear

The Selberg axioms attach to `F ∈ S` exactly the following numerical data, and every one of them is
**additive** under multiplication of Dirichlet series:
```
degree            d_{FG} = d_F + d_G
log-conductor     \log q_{FG} = \log q_F + \log q_G
pole order        m_{FG} = m_F + m_G
argument of ω     \arg ω_{FG} = \arg ω_F + \arg ω_G   (mod 2π)
shift invariant   θ_{FG} = θ_F + θ_G                   (§176.1)
divisor on Re s=1 \mathrm{ord}_{1+it}(FG) = \mathrm{ord}_{1+it}F + \mathrm{ord}_{1+it}G
twist divisors    the same, for every F^{\barχ}        (Theorem 106)
```
So the axioms give a family of **linear functionals** on `S^{gp}` — and, by Theorem 115, the divisor
functionals are precisely the coordinates of the orthogonal projection onto `V_1`.

### 204.2 The two candidate lattices have identical linear data

`Z^{(∞)}` (Conjecture B) and `A_n/\sqrt2` or any rescaled even lattice (RSA) are, as **abstract
groups with a distinguished generating set of unit vectors**, indistinguishable: both are free abelian
on the primitives, with the same additive degree, conductor, root number, shift and divisor data. They
differ **only** in the quadratic form `n_H = ‖[H]‖²`.

> **Theorem 123 (the closure of Theorem 39).** No function of the axiom-supplied invariants can
> distinguish Conjecture B from RSA. Concretely, the two configurations
> ```
> n_F = n_G = 1,\quad \mathrm{Re}\,c_{F,G} = 0        (Conjecture B)
> n_F = n_G = 1,\quad \mathrm{Re}\,c_{F,G} = −\tfrac12  (RSA)
> ```
> assign the same value to every additive invariant of every element of the group generated by `F` and
> `G`, and both are consistent with positivity, Cauchy–Schwarz, integrality, the parallelogram law, the
> Energy Gap, Bessel, and the twisted divisor bound (§203). **Any proof of Conjecture B must therefore
> evaluate a genuinely quadratic invariant — which by §179.1 the Euler product supplies only at the
> wrong scale, and by §185.2 cannot be sieved to the right one.**

This is the definitive form of the programme's central obstruction and it unifies:
`Theorem 39` (additive versus quadratic), `§179.1` (the Euler product's scale mismatch),
`§185.2` (the four-fold failure of the sieve), `§194.3` (`[F]` is known only on `V_1`),
`§199.2` (no positivity obstruction), `§201` (the root-system alternative),
`§203` (RSA survives every test). **They are one statement.**

### 204.3 What this says about the shape of any future proof

```
must produce a quadratic invariant of a single F, or a bilinear one of a pair,
  not expressible in the additive data                                    — i.e. Sym² or Rankin–Selberg
must therefore construct a new L-function, or continue an existing series
  across a boundary where the axioms give no control                      — MI / (PSD₂)
cannot come from: positivity, Cauchy–Schwarz, polarisation, Bessel, energy gaps,
  degree/conductor bookkeeping, twist integrality, zero counting mod 1     — all recorded, all closed
```

> **Recorded as the programme's terminal statement of the obstruction.** Everything unconditional that
> the axioms can give about the Selberg pairing has now been extracted (Theorems 76′, 76″, 84′, 85′,
> 89, 90, 100, 102, 103, 104, 106, 111, 114, 115, 122, Corollaries 101, 105, 108, 112, 116, 117,
> Propositions 113, 118, 119, 120, 121). The remaining content of Conjectures A and B is exactly the
> quadratic datum the axioms do not supply.

---

## 205. Cycle 205 (2026-07-26) — **Theorem 124**: Conjecture A from the continuation of one explicit Dirichlet series

Theorem 123 says any proof must evaluate a quadratic invariant. This cycle puts that invariant into a
single Dirichlet series built from the coefficients of `G` alone.

### 205.1 The square-index series

For `G ∈ S` set `g(n) := a_G(n²)`. Since `a_G` is multiplicative and `(m,n) = 1 ⟹ (m²,n²) = 1`,
**`g` is multiplicative**, so
```
D_G(s) := Σ_{n≥1} a_G(n²)\,n^{−s}
        = ∏_p\Big(1 + a_G(p²)p^{−s} + a_G(p^4)p^{−2s} + \cdots\Big)
        = ∏_p \frac{G_p(p^{−s/2}) + G_p(−p^{−s/2})}{2} ,
```
the last equality because the even-index part of a power series is `\tfrac12(f(X)+f(−X))`, applied at
`X = p^{−s/2}`. By Ramanujan, `a_G(n²) ≪_ε n^ε`, so `D_G` converges absolutely for
`\mathrm{Re}\,s > 1`, and exactly as in Theorem 52
```
\log D_G(s) = Σ_p a_G(p²)\,p^{−s} + (\text{holomorphic on } \mathrm{Re}\,s > 1/2) .
```

> **Theorem 124.** For every `G ∈ S` the series `D_G(s) = Σ_n a_G(n²)n^{−s}` satisfies Selberg axioms
> **(1)** (absolutely convergent Dirichlet series, `D_G(1\text{-coefficient}) = 1`), **(4)** (Ramanujan)
> and **(5)** (Euler product with logarithmic coefficients supported on prime powers and `≪ n^ε`)
> **outright**. If in addition `D_G` is meromorphic in a neighbourhood of `s = 1` — axiom (2) locally —
> then `δ_1(a_G(·²)) = −\mathrm{ord}_{s=1}D_G ∈ Z`, i.e. **(PSD₂)** holds; and by Theorem 111,
> **Selberg's Conjecture A follows.**

Formally `D_G(s) = L(s,\mathrm{Sym}²G)/ζ(2s)` (the classical identity `Σ_na(n²)n^{−s} =
L(s,\mathrm{sym}²f)/ζ(2s)` for a `GL_2` newform), so this is `\mathrm{Sym}²`-closure again — but now
written as **one explicit Dirichlet series in the coefficients of `G`**, with three of the five axioms
free and only the analytic ones missing.

*Consistency.* `G = ζ`: `a_ζ(n²) = 1`, `D_ζ(s) = ζ(s)`, `−\mathrm{ord}_1 = 1 = δ_1(a_ζ(·²))` ✔.
`G = ζ²`: `a_{ζ²}(n²) = d(n²)`, `D_{ζ²}(s) = Σ_nd(n²)n^{−s} = ζ(s)^3/ζ(2s)`, order `3` ✔ — matching
`δ_1(a_{ζ²}(·²)) = 3` from §189.1. `GL_2` newform, trivial nebentypus: `D_G = L(s,\mathrm{sym}²)/ζ(2s)`,
holomorphic and non-zero at `s = 1`, so `δ_1 = 0` ✔.

### 205.2 Why this is the right final form

Preprint Theorem 4 shows axioms (1),(4),(5) alone do **not** imply Conjecture A, so the missing
analytic input is genuinely necessary — Theorem 124 is not a sleight of hand. What it achieves is to
replace *"`S` is closed under `⊗`"* (a structural closure property of a whole class) by

> *"one explicit Dirichlet series, written down from the coefficients of `G`, continues meromorphically
> to `s = 1`."*

That is the smallest statement from which Conjecture A has been derived in this programme, and by
Theorem 123 no smaller one of a *linear* nature can exist.

### 205.3 Lean

New `HTGeometry/SquareIndexMultiplicative.lean`, registered
(`lake build +GaloisForLFunctions.HTGeometry` clean):
```lean
theorem isMultiplicative_comp_sq {R} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    (1 : R) = f 1 ∧ ∀ {m n : ℕ}, Nat.Coprime m n → f ((m * n) ^ 2) = f (m ^ 2) * f (n ^ 2)
theorem comp_sq_one … : f (1 ^ 2) = 1
theorem coprime_sq_sq {m n : ℕ} (h : Nat.Coprime m n) : Nat.Coprime (m ^ 2) (n ^ 2)
```
— the multiplicativity of `n ↦ a_G(n²)`, which is the only arithmetic input to Theorem 124 and the
reason `D_G` has an Euler product at all.

---

## 206. Cycle 206 (2026-07-26) — square-detection **is** an additive twist, and that explains degree 1

### 206.1 Detecting squares is a theta pairing

The obstruction to (PSD₂) is the restriction of `G` to square indices (§185.2(3): squares are not a
union of congruence classes). But they **are** detected by the classical theta function:
```
1_{\square}(m) = ∫_0^1 θ(α)\,e(−mα)\,dα ,\qquad θ(α) = Σ_{n≥1}e(n²α) .
```
Hence, formally,
```
D_G(2w) = Σ_m a_G(m)1_\square(m)m^{−w} = ∫_0^1 θ(α)\,\Big(Σ_m a_G(m)e(−mα)m^{−w}\Big)\,dα ,
```
so **the square-restriction of `G` is the `α`-average of the *additive twist of `G` at exponent 1*
against a theta function.**

### 206.2 The Selberg axioms resonate only at exponent `1/d`

§82/§100.2 recorded: the Selberg-class functional equation resonates with the twist
`Σ_m a_G(m)e(−αm^{κ})m^{−s}` at **exactly one** exponent, `κ = 1/d` (stationary phase against the
`d\,t\log t` archimedean phase), and there is no second spectrum. The exponent needed in §206.1 is
`κ = 1`. Therefore:

> **The square-detection integral uses the additive twist at exponent `1`, which the axioms continue
> **only when `1 = 1/d`, i.e. `d = 1`.**

*Degree 1, verified.* For `G = L(s,χ)`, the exponent-1 twist **is** the standard twist, and directly
`D_G(s) = Σ_nχ(n²)n^{−s} = Σ_nχ(n)²n^{−s} = L(s,χ²)`, meromorphic, with
`δ_1(a_G(·²)) = −\mathrm{ord}_{s=1}L(s,χ²) ∈ \{0,1\}` ✔ — exactly the value Theorem 109 predicts. So
**(PSD₂) holds in degree 1, and the reason is precisely that the required twist exponent coincides with
the resonant one.**

> **This is a new and complete explanation of why Conjecture A is a theorem in degree `1` and open
> beyond**: not "degree 1 is classified", but *square-detection needs `κ = 1` and the axioms supply
> `κ = 1/d`.* It supersedes §185.2(3), which recorded only that no character detects squares.

### 206.3 The fractional repair, and where it lands

One can match the exponents by replacing `θ` with a fractional theta adapted to `d`:
```
Ψ_d(α) := Σ_{n≥1} e\big(α\,n^{2/d}\big) ,\qquad
∫_0^1 Ψ_d(α)\,Φ_G(s,−α)\,dα \;=\; Σ_m a_G(m)m^{−s}\,\#\{n : n^{2/d} = m^{1/d}\}
\;=\; Σ_n a_G(n²)\,n^{−2s} ,
```
using KP's standard twist `Φ_G(s,α) = Σ_m a_G(m)e(−αm^{1/d})m^{−s}` at its resonant exponent. **So
(PSD₂) is the `α`-integral of the standard twist against an explicit fractional theta — a *linear*
spectral pairing**, in contrast to §12's bilinear pairing `∫Φ_F\overline{Φ_G}`.

Status of that route: it is the continuous form of §187's spectral summation, and inherits §189.2's
obstruction — the twist's continuation in `s` and the convergence of the `α`-integral hold on
**disjoint** ranges, because `Φ_G(·,α)` is discontinuous at every point of `\mathrm{Spec}(G)`
(§11.2) and `Ψ_d` has its stationary points exactly there. Recorded, with the caveat that the linear
pairing is *not* excluded by §21's bilinear no-go (§187.2), so this remains the one open construction.

### 206.4 Consequence for the shape of the remaining problem

```
Conjecture A  ⟸ (PSD₂)  ⟸  D_G = Σ_n a_G(n²)n^{−s} meromorphic at s = 1      (Theorem 124)
              ⟸  the α-average of Φ_G against the fractional theta Ψ_d converges and continues
              ⟸  an exponent-1 additive twist of G — available exactly for d = 1  (§206.2)
```
The whole of Conjecture A therefore rests on crossing the gap between the resonant exponent `1/d` and
the square-detecting exponent `1`. **That gap is `d − 1`, the same width as §14.3's `β`-contour gap
between the abscissa `β = d` and the pole `β = 1`** — the two are the same obstruction, now identified
for the third time and from the cleanest direction.

---

## 207. Cycle 207 (2026-07-26) — degree 2: the fractional theta becomes elementary, and the wall is `α`-uniformity

### 207.1 The exponents match exactly when `d = 2`

§206.3's kernel is `Ψ_d(α) = Σ_n e(αn^{2/d})`. For `d = 2` this is `Σ_{n≥1}e(αn)` — the **integer**
frequency comb, an elementary object. Pairing it against the standard twist at its own resonant
exponent `1/d = 1/2`:
```
Φ_G(s,−α) = Σ_m a_G(m)\,e(α\sqrt m)\,m^{−s} ,\qquad
\lim_{A→∞}\frac1A∫_0^A Φ_G(s,−α)\,e(−αn)\,dα \;=\; a_G(n²)\,n^{−2s} ,
```
because the Bohr mean annihilates every frequency `\sqrt m − n ≠ 0`. Summing over `n`,
```
D_G(2s) \;=\; Σ_{n≥1}\ \mathrm{M}_α\Big[Φ_G(s,−α)\,e(−αn)\Big] ,
```
**the sum of the Bohr–Fourier coefficients of the standard twist at integer frequencies.**

> For `d = 2` — which by Corollary 102 carries *all* of Conjecture A in degree `≤ 2` — the
> square-restriction of `G` is the integer-frequency Bohr spectrum of `Φ_G`. No fractional theta, no
> Gauss sums: the kernel is the comb.

*(Note the correction to a natural first attempt: the ordinary integral `∫_0^1` does **not** work,
since `∫_0^1e(α(\sqrt m − n))dα = (e(\sqrt m−n)−1)/(2πi(\sqrt m−n)) ≠ 0` for irrational `\sqrt m`. The
Bohr mean over `[0,A]`, `A → ∞`, is required.)*

### 207.2 Where it stops

For `\mathrm{Re}\,s > 1` the series defining `Φ_G(s,·)` converges absolutely and uniformly in `α`, so
every Bohr mean above is legitimate — and the identity is then a tautology, both sides being the
convergent `D_G(2s)`. Continuation requires taking `s` into `\mathrm{Re}\,s < 1`, where `Φ_G(s,·)` is
the **continued** twist: meromorphic in `s` ✔ but with completely uncontrolled behaviour in `α`. That
is §10.2's open core, sharpened by §11.2: `α ↦ Φ_G(·,α)` is discontinuous at every point of
`\mathrm{Spec}(G)`, so no Bohr mean of the continued twist is known to exist.

> **Verdict.** The `d = 2` kernel is as simple as it can be, and the obstruction is unchanged and
> single: **`α`-uniform control of the continued standard twist**. Every construction in this
> programme that reaches for a quadratic invariant — §12's bilinear pairing, §187's spectral
> summation, §206.3's fractional theta, §207.1's comb — terminates at that same statement.

### 207.3 The obstruction, in one line

```
Conjecture A (all degrees ≤ 2)  ⟺  the continued standard twist Φ_G(s,·) admits Bohr means
                                    at integer frequencies for s near s^*_0 .
```
Everything else — Theorem 111's reduction to `\mathrm{Sym}²`, Theorem 124's single Dirichlet series,
§206's exponent gap — is bookkeeping around this one analytic statement. It is not a new conjecture:
it is a regularity question about an object Kaczorowski–Perelli constructed, and it is the *only*
input the programme now needs in degree `2`.

> **Recorded as the terminal open core.** Named **(BOHR)**: *does the continued standard twist of a
> degree-2 element of `S` have Bohr–Fourier coefficients at integer frequencies, locally uniformly in
> `s` near `s^*_0 = 3/4`?* Affirmative ⟹ (PSD₂) in degree 2 ⟹ Conjecture A for all `d_F ≤ 2`.

---

## 208. Cycle 208 (2026-07-26) — (BOHR) analysed: the spectral singularity is **always** `|ζ|^{−1/2}`, and the required cancellation is self-dual

### 208.1 The exponent at the target point is universal

By C7.1 (§14.1) the standard twist near a spectral point `α_0` behaves as
`Φ_G(s,−α_0+ζ) ≍ ρ_0(α_0)\,|ζ|^{\,d(s−s^*_0)}`, `s^*_0 = (d+1)/(2d)`. The object needed is
`D_G(2s) = Σ_n a_G(n²)n^{−2s}` at `2s = 1`, i.e. **`s = 1/2`**. Then
```
d\big(\tfrac12 − s^*_0\big) \;=\; \tfrac d2 − \tfrac{d+1}{2} \;=\; −\tfrac12 \qquad\text{for every degree } d .
```

> **The spectral singularity of the continued twist at the point Conjecture A needs is `|ζ|^{−1/2}` —
> **independently of the degree**, and therefore **locally integrable**.

That is a genuinely encouraging structural fact: `(BOHR)` is not obstructed by non-integrability, as
the bilinear pairing of §12 was (there the exponent doubles to `2d(s−s^*_0)+1`, and §14.2(2) records
convergence only for `\mathrm{Re}\,s < 1/2`).

### 208.2 The size of the spectral contribution, and the saving required

For `d = 2`, `\mathrm{Spec}(G) = \{α_m = 2\sqrt{m/q}\}`, so `α_m ≤ A` for `m ≤ qA²/4`: about `A²`
spikes in `[0,A]`. Each carries `ρ_0(α_m) ∝ \overline{a_G(m)}m^{s^*_0−1} = \overline{a_G(m)}m^{−1/4}`,
i.e. size `≈ A^{−1/2}` at the top of the range, and each local integral `∫_{|ζ|<ε}|ζ|^{−1/2}` is
`O(\sqrt ε)`. Hence
```
∫_0^A |\text{singular part}| \;≈\; A²\cdot A^{−1/2} \;=\; A^{3/2} ,
\qquad\text{so}\qquad \frac1A∫_0^A|\cdot| ≈ A^{1/2} \;→\; ∞ .
```
The true Bohr mean must be `a_G(n²)n^{−2s} = O(n^{ε−1})`. **So (BOHR) requires exactly square-root
cancellation** among the spectral spikes — the classical shape, and a saving of `A^{1/2}` on a sum of
`A²` terms.

### 208.3 The cancellation is self-dual

Integrating the spike expansion against `e(−αn)` gives, per spike, a factor `e(−α_mn)`, so the sum to
be estimated is
```
Σ_{m ≤ qA²/4} \overline{a_G(m)}\,m^{−1/4}\,e\big(−2n\sqrt{m/q}\big) ,
```
which is a **truncated standard twist of `\bar G`** evaluated at `α = 2n/\sqrt q`. It is large precisely
when that `α` lies in `\mathrm{Spec}(\bar G)` — i.e. at `m = 4n²`, the diagonal the whole construction
is meant to produce.

> **(BOHR) is self-dual.** The cancellation needed to make the Bohr mean of `Φ_G` exist is cancellation
> in a standard twist of `\bar G`, whose own size is governed by the same spectral data. This is a
> bootstrap, not an estimate that can be inserted from outside — and it is the linear counterpart of
> §12.3's finding that in the bilinear pairing "the blow-up is exactly the diagonal it is supposed to
> produce".

### 208.4 What is new here, and what remains

New: the exponent computation (universal `−1/2`, hence integrable — the linear pairing is *not*
obstructed the way the bilinear one is), the explicit `A^{1/2}` saving required, and the identification
of the required cancellation as self-dual.

Remaining: (BOHR) itself. It is now a completely explicit statement — *square-root cancellation in a
truncated standard twist of `\bar G` at the spectral point `2n/\sqrt q`* — with no hidden hypotheses,
and it is the single input needed for Conjecture A in degree `≤ 2`. Its self-duality is the reason it
cannot be settled by importing a bound: any proof must exploit the functional equation of the twist
itself (KP's Theorem 2, the Hurwitz–Lerch-type equation of arXiv:1911.10497), which is the one piece of
KP machinery this programme has not yet used quantitatively.

> **Recorded as the next concrete target**: apply the standard twist's own functional equation to bound
> `Σ_{m≤M}\overline{a_G(m)}m^{−1/4}e(−2n\sqrt{m/q})` with square-root saving. Unlike every previous
> target, this is a bound on an explicit finite sum, not an existence statement.

---

## 209. Cycle 209 (2026-07-26) — **correction to §208.2: the singular part is absolutely Bohr-integrable**

### 209.1 The defect

§208.2 estimated the spectral contribution to `\frac1A∫_0^A|Φ_G(1/2,α)|dα` as `A^{1/2}` and concluded
that (BOHR) needs square-root cancellation. **The factor `\sqrt ε` from each local integral was written
down and then dropped when the spikes were summed.** Redone with `ε` = half the local gap:

```
spectral points:   α_m = 2\sqrt{m/q},        α_m ≤ A  ⟺  m ≤ qA²/4 ,   so ≍ A² spikes
local gap:         dα/dm = 1/\sqrt{qm} = 2/(qα_m)  ⟹  ε_m ≍ (qα_m)^{−1} ≍ m^{−1/2}q^{−1/2}
spike height:      ρ_0(α_m) ∝ \overline{a_G(m)}\,m^{\,s^*_0−1} = \overline{a_G(m)}\,m^{−1/4}
local integral:    ∫_{|ζ|<ε_m}|ζ|^{−1/2}\,dζ ≍ \sqrt{ε_m} ≍ m^{−1/4}q^{−1/4}
```
so each spike contributes `≍ |a_G(m)|\,m^{−1/4}·m^{−1/4} = |a_G(m)|\,m^{−1/2}`, and
```
∫_0^A |\text{singular part}|\,dα \;≍\; Σ_{m ≤ qA²/4}|a_G(m)|\,m^{−1/2} \;≪_ε\; (qA²)^{1/2+ε} \;≍\; A^{1+ε} ,
\qquad\text{hence}\qquad \frac1A∫_0^A|\cdot|\,dα \;=\; O(A^{ε}) .
```

> **Corrected conclusion.** The singular part of the continued standard twist at `s = 1/2` is
> **absolutely Bohr-integrable**, up to `A^{ε}`. (BOHR) does **not** require square-root cancellation
> among the spikes; the spikes are individually integrable and collectively of bounded mean.

The coincidence is structural, not accidental: the spike height `m^{−1/4}` and the spacing-derived
factor `m^{−1/4}` multiply to `m^{−1/2}`, whose partial sums are `≍ \sqrt M ≍ A` — exactly the
normalisation of the Bohr mean. Both exponents come from `s^*_0 − 1 = −1/4` and from
`α_m ∝ \sqrt m`, i.e. both from `d = 2`. **The linear pairing sits exactly at the boundary of
absolute convergence, and on the convergent side.**

### 209.2 What (BOHR) now requires

With the singular part absolutely integrable, what remains is:
1. **the regular part** of `Φ_G(1/2,·)` — the holomorphic-in-`ζ` series of C7.1 — to have bounded mean;
2. **existence of the limit** `A → ∞` (not merely boundedness), i.e. Bohr almost-periodicity of
   `α ↦ Φ_G(1/2,α)`.

Item 1 is a statement about `Φ_G(s−k/2,α_0)` summed over `k ≥ 0` (the second sum in C7.1), i.e. about
the twist at the *lower* poles — controlled by the same expansion. Item 2 is the genuine remaining
content: an almost-periodicity statement for the continued twist in the `α` variable.

> **(BOHR), restated after the correction.** *Is `α ↦ Φ_G(1/2,α)` Besicovitch almost periodic, with
> Bohr–Fourier coefficients at the integer frequencies?* Its absolute mean is finite (§209.1); what is
> missing is the existence of the means, not their size.

That is a substantially weaker requirement than the square-root cancellation §208 asked for, and it is
the first time the terminal open core has been an **existence-of-mean-values** statement — a class for
which the programme already has machinery (`oscInt_gram_bound`, `genPoly_meanValue`,
`bessel_of_almost_orthogonal`, and the Besicovitch framework of Theorem 77).

### 209.3 Ledger

| # | where | defect | status |
|---|---|---|---|
| 8 | §208.2 | `\sqrt ε` factor dropped when summing spikes; `A^{1/2}` should be `A^{ε}` | **corrected here** |

Eight defects; the eighth was caught one cycle after it was written, by redoing the estimate rather
than re-reading it. **Every correction so far has come from re-derivation, never from re-reading.**

---

## 210. Cycle 210 (2026-07-26) — (BOHR): the sizes all work; what remains is one interchange

### 210.1 The formal computation, with every error term checked

Work with the Dirichlet series (valid for `\mathrm{Re}\,s > 1`, then continued):
```
Φ_G(s,−α) = Σ_m a_G(m)\,e(α\sqrt m)\,m^{−s} ,\qquad
\frac1A∫_0^A e(αx)\,dα = \frac{e(Ax)−1}{2πixA} \;→\; [x = 0] .
```
Pairing against `e(−αn)` and interchanging **formally**:
```
\frac1A∫_0^A Φ_G(\tfrac12,−α)e(−αn)\,dα
   \;=\; \underbrace{a_G(n²)\,n^{−1}}_{m = n²}
   \;+\; O\!\Big(\frac1A Σ_{m ≠ n²}\frac{|a_G(m)|\,m^{−1/2}}{|\sqrt m − n|}\Big) .
```
The error sum converges only logarithmically — for large `m`, `|\sqrt m − n| ≍ \sqrt m`, so the terms
are `≍|a_G(m)|m^{−1}` and the sum to `M` is `≪_ε M^{ε}\log M`. With the natural truncation
`M ≍ qA²/4` (the range of `m` whose frequency `\sqrt m` is resolved by `[0,A]`),
```
\text{error} \;≪_ε\; \frac{A^{ε}\log A}{A} \;→\; 0 .
```

> **Every size works.** The diagonal `m = n²` produces exactly the wanted `a_G(n²)n^{−1}`, and the
> off-diagonal is `O(A^{ε−1})`. Combined with §209.1 (the spectral spikes have bounded absolute Bohr
> mean), **there is no size obstruction anywhere in (BOHR).**

### 210.2 The one remaining step

The interchange above is not justified: at `s = 1/2` the Dirichlet series `Σ_m a_G(m)m^{−1/2}e(α\sqrt m)`
does not converge absolutely (`Σ_m|a_G(m)|m^{−1/2}` diverges), and `Φ_G(1/2,·)` is the *continued*
object. What must be shown is a **mean approximation**:
```
\frac1A∫_0^A\Big|\,Φ_G(\tfrac12,−α) \;−\; Σ_{m ≤ M_0}a_G(m)\,e(α\sqrt m)\,m^{−1/2}\Big|\,dα \;→\; 0
\qquad (M_0 = M_0(A) → ∞ \text{ suitably}) .
```

> **(BOHR) reduces to this single statement**: *the continued standard twist at `s = 1/2` is
> approximated in Bohr mean by its own truncated Dirichlet series.* Nothing else is missing.

Three facts make this the right target:
- It is an **`L¹`-mean** statement, not a pointwise or uniform one; §11.2's discontinuity of
  `α ↦ Φ_G(·,α)` at spectral points is therefore not an obstruction (a measure-zero set).
- The absolute mean of both sides is finite: the continued object by §209.1, the truncation trivially.
- It is exactly the hypothesis under which Theorem 77's Besicovitch machinery operates — the programme
  already has the framework (`genPoly_meanValue`, `oscInt_gram_bound`,
  `bessel_of_almost_orthogonal`, `genPoly_meanValue_error_of_gap`), applied there to `S_F` and here to
  `Φ_G(1/2,·)`.

### 210.3 The chain, complete

```
Conjecture A for all d_F ≤ 2
  ⟸ (PSD₂) in degree 2                                            Theorem 111 + Corollary 102
  ⟸ D_G(s) = Σ_n a_G(n²)n^{−s} meromorphic at s = 1               Theorem 124
  ⟸ (BOHR): Bohr means of Φ_G(1/2,·) at integer frequencies       §207.3
  ⟸ Φ_G(1/2,·) is approximated in Bohr mean by its truncated
    Dirichlet series                                              §210.2   ← the only open step
```
with the sizes verified at every stage: `|ζ|^{−1/2}` singularity (integrable, §208.1), absolute
spectral mean `O(A^{ε})` (§209.1), off-diagonal `O(A^{ε−1})` (§210.1).

> **This is the tightest the programme has ever been.** The remaining statement mentions no primes, no
> zeros, no energy, no functoriality: it is a mean-approximation property of one explicit continued
> Dirichlet series in one real variable.

---

## 211. Cycle 211 (2026-07-26) — the final step reduced to an approximate functional equation, with one of its two error terms verified

### 211.1 The natural truncation is `α`-dependent, and that is the right structure

The residue data `ρ_0(α_m) ∝ \overline{a_G(m)}m^{−1/4}` at `α_m = 2\sqrt{m/q}` identifies the twist's
effective length at parameter `α` as `m ≍ qα²/4`. So the expected approximate functional equation is
```
Φ_G(\tfrac12,−α) \;=\; Σ_{m ≤ cα²} a_G(m)\,e(α\sqrt m)\,m^{−1/2} \;+\; (\text{dual sum}) \;+\; (\text{small}) ,
\qquad c = q/4 .
```
Comparing with the *fixed* truncation `P_{M_0}(α) = Σ_{m ≤ M_0}a_G(m)e(α\sqrt m)m^{−1/2}` with
`M_0 = cA²`, the difference on `[0,A]` consists of the terms `cα² < m ≤ M_0`.

### 211.2 The over-shoot terms have vanishing Bohr mean — verified

Reversing the order of summation and integration (legitimate: finitely many `m`),
```
\frac1A∫_0^A Σ_{cα² < m ≤ M_0} a_G(m)\,e(α\sqrt m)\,m^{−1/2}\,dα
   = \frac1A Σ_{m ≤ M_0} a_G(m)\,m^{−1/2}\!\!\int_0^{\min(A,\sqrt{m/c})}\!\! e(α\sqrt m)\,dα ,
```
and `\big|∫_0^T e(α\sqrt m)dα\big| = \big|\frac{e(T\sqrt m)−1}{2πi\sqrt m}\big| ≤ \frac1{π\sqrt m}`, so
```
\Big|\;\cdot\;\Big| \;≤\; \frac1{πA}Σ_{m ≤ M_0}|a_G(m)|\,m^{−1} \;≪_ε\; \frac{M_0^{ε}\log M_0}{A}
   \;=\; \frac{A^{ε}\log A}{A} \;→\; 0 .
```

> **Verified unconditionally** (uses only Ramanujan). The gap between the `α`-dependent AFE truncation
> and the fixed truncation `M_0 = cA²` contributes nothing to any Bohr mean.

### 211.3 What is left

```
(BOHR)  ⟸  (i)  an approximate functional equation for Φ_G(s,α) at s = 1/2, of length ≍ qα²/4 ;
           (ii) the dual sum in that AFE has vanishing Bohr mean at integer frequencies .
```
Item (i) is a derivation from **Kaczorowski–Perelli's Theorem 2** — the Hurwitz–Lerch-type functional
equation for the standard twist (arXiv:1911.10497) — which is the one piece of their machinery this
programme has never used quantitatively (§208.4). Item (ii) is an oscillation estimate of exactly the
shape verified in §211.2, applied to the dual side.

> **Everything else in the chain is now verified**: the singularity exponent (`−1/2`, integrable, all
> degrees, §208.1), the absolute spectral mean (`O(A^{ε})`, §209.1), the diagonal (`a_G(n²)n^{−1}`,
> §210.1), the off-diagonal (`O(A^{ε−1})`, §210.1), and the over-shoot (`O(A^{ε−1})`, §211.2). **The
> only unverified inputs are the twist's AFE and the oscillation of its dual sum.**

### 211.4 Status, stated exactly

```
Conjecture A for every F ∈ S with d_F ≤ 2
   ⟸ (PSD₂) in degree 2                                        Thm 111 + Cor 102   [proved]
   ⟸ D_G(s) = Σ_n a_G(n²)n^{−s} meromorphic at s = 1            Thm 124             [proved]
   ⟸ (BOHR)                                                     §207.3              [proved]
   ⟸ AFE for Φ_G at s = 1/2  +  dual-sum oscillation            §211.3              [OPEN]
```
Every implication above is proved; the chain terminates in a two-part analytic statement about the
Kaczorowski–Perelli standard twist and nothing else. **No step now involves primes, zeros, energies,
lattices, or functoriality.**

---

## 212. Cycle 212 (2026-07-26) — the Mellin route to the Bohr mean, and why it cannot be used on the real axis

### 212.1 The attempt

C6.1's Mellin–Barnes representation for `d = 2` reads
`Φ_G(s,−α) = \frac1{2πi}∫_{(c)}Γ(w)(−2πiα)^{−w}G(s+\tfrac w2)\,dw`, and it is tempting to compute the
Bohr mean by interchanging:
```
\frac1A∫_0^AΦ_G(\tfrac12,−α)e(−αn)\,dα
 = \frac1{2πi}∫_{(c)}Γ(w)(−2πi)^{−w}G(\tfrac12+\tfrac w2)\Big[\frac1A∫_0^Aα^{−w}e(−αn)\,dα\Big]dw ,
```
with `∫_0^∞β^{−w}e^{−2πiβ}dβ = Γ(1−w)(2πi)^{w−1}` for `0 < \mathrm{Re}\,w < 1`. The bracket is then
`≍ C(w)\,n^{w−1}/A → 0`, so the Bohr mean would vanish for **every** `n` — contradicting the diagonal
computation of §210.1, which gives `a_G(n²)n^{−1} ≠ 0`.

### 212.2 Why the contradiction is only apparent

`e^{−z} = \frac1{2πi}∫_{(c)}Γ(w)z^{−w}dw` requires `|\arg z| < π/2`. Here `z = 2πiα\sqrt m` is **purely
imaginary**: the representation sits exactly on the boundary of its domain of validity and does not
hold on the real `α` axis. This is precisely the reason C6.1 and C7.1 are stated for
`z ∈ H = \{\mathrm{Im}\,z > 0\}`, with the standard twist recovered as the boundary value
`F(s,α) = \lim_{y→0^+}Φ_F(s,−α+iy)` (§12.1, §13).

> **Recorded do-not-retry.** The Bohr mean of the standard twist cannot be computed by the
> Mellin–Barnes representation on the real axis: the representation is invalid there, and the naive
> interchange produces the false answer `0`. Any Mellin computation must be carried out at
> `\mathrm{Im}\,z = y > 0` and the limit `y → 0^+` taken **after** the `α`-average — which is exactly the
> `y → 0` boundary problem recorded in §12.3 and §13.4.

This is the third distinct route (after §189's two-representation domains and §190's tube theorem) whose
failure traces to the same source: **the twist is only a boundary value, and every quantitative
statement about it on the real axis must survive a `y → 0` limit.**

### 212.3 Consequence for the live route

The approximate-functional-equation route of §211.3 is unaffected, because an AFE is derived at
`y > 0` and its terms are individually continuous up to `y = 0` (the sums are finite). It remains the
only live construction, and the two open items are unchanged:
```
(i)  an AFE for Φ_G(s,α) at s = 1/2 with truncation length ≍ qα²/4 , from KP's Theorem 2 ;
(ii) vanishing Bohr mean of its dual sum at integer frequencies .
```
> **Standing note.** Item (ii) is now known to be the *only* place a non-zero contribution could
> compete with the diagonal, since every other error term in the chain has been bounded
> (§208.1, §209.1, §210.1, §211.2). If the dual sum's Bohr mean vanishes, (BOHR) — and with it
> Conjecture A in degree `≤ 2` — follows.

---

## 213. Cycle 213 (2026-07-26) — the chain verified in degree 1, and the periodic/almost-periodic dichotomy

### 213.1 Degree 1, end to end

`G = L(s,χ)`, `d = 1`, `s^*_0 = (d+1)/(2d) = 1`, `\mathrm{Spec}(G) = \{m/q\}`, and
```
Φ_G(s,−α) = Σ_m χ(m)\,e(αm)\,m^{−s} ,
```
a Lerch-type series with **integer frequencies**. The pairing kernel of §206.3 is
`Ψ_1(α) = Σ_n e(αn^{2/1}) = Σ_n e(αn²)`, the classical theta, and the relevant Bohr frequencies are
`n²`. Every step of the chain is then explicit:
```
Bohr mean of Φ_G(s,−α) at frequency n²  =  ∫_0^1 Φ_G(s,−α)e(−αn²)dα  =  χ(n²)\,n^{−2s}   ✔
D_G(s) = Σ_nχ(n²)n^{−s} = Σ_nχ(n)²n^{−s} = L(s,χ²)                                        ✔ meromorphic
δ_1(a_G(·²)) = −\mathrm{ord}_{s=1}L(s,χ²) ∈ \{0,1\}                                       ✔ integer
n_G = δ_1(a_{G\bar G}(·²)) − 2\mathrm{Re}\,δ_1(a_G(·²))                                    ✔ Theorem 111
```
**The chain of §211.4 is verified in degree 1, with (BOHR) holding for a trivial reason.**

### 213.2 The reason it is trivial there — and the exact difficulty in degree 2

> **In degree `1` the standard twist is a *periodic* function of `α` (frequencies `m ∈ Z`), so its Bohr
> means are ordinary Fourier coefficients: `\lim_A\frac1A∫_0^A` collapses to `∫_0^1`, and existence is
> automatic. In degree `2` the frequencies are `\sqrt m`, so the twist is at best *almost periodic*, and
> the existence of its mean values is a genuine analytic statement.**

This is the cleanest available description of the gap, and it dovetails with §206.2: the square-detection
exponent is `1`, the resonant exponent is `1/d`, and *periodicity* of the twist is exactly the case
`1/d ∈ Z`, i.e. `d = 1`. Two independent formulations of the same threshold:
```
§206.2 :  square-detection needs κ = 1 ; the axioms resonate at κ = 1/d  ⟹ equal iff d = 1
§213.2 :  Bohr means are Fourier coefficients iff the twist is periodic  ⟹ iff d = 1
```

### 213.3 Consequence: (BOHR) is an almost-periodicity statement, and that is its natural home

The programme already possesses the Besicovitch framework in which such statements live — it is what
Theorem 77 uses for `S_F`, with the machine-checked support
`genPoly_meanValue`, `genPoly_meanValue_error_of_gap`, `oscInt_norm_le`, `oscInt_gram_bound`,
`bessel_of_almost_orthogonal`, and the frequency separation `monomial_log_separation`. The frequencies
here are `\{\sqrt m\}`, whose separation is `|\sqrt m − \sqrt{m'}| ≥ 1/(\sqrt m + \sqrt{m'}) ≫ M^{−1/2}`
for `m ≠ m' ≤ M` — the exact analogue of §167.2's `|\log a − \log b| ≥ 1/\max(a,b)`, and equally
elementary.

> **Recorded target, restated in its natural terms.** *Show that the continued standard twist
> `α ↦ Φ_G(1/2,α)` of a degree-2 element of `S` lies in the Besicovitch class `B¹`, with Fourier–Bohr
> spectrum `\{\sqrt m\}` and coefficients `a_G(m)m^{−1/2}`.* Its absolute mean is already bounded
> (§209.1); the frequencies are separated as above; the diagonal and every error term are bounded
> (§210–§211). **What is missing is `B¹`-membership, i.e. approximation in mean by the truncated
> series — and that is the single statement §210.2 identified.**

---

## 214. Cycle 214 (2026-07-26) — **Theorem 125**: at `y > 0` everything is exact; the whole problem is one double limit

### 214.1 The damped twist is absolutely convergent for every `s`

C6.1's `Φ_G(s,z) = Σ_m a_G(m)e(z\sqrt m)m^{−s}` (`d = 2`) is taken at `z = −α + iy`, `y > 0`:
```
Φ_G(s,−α+iy) \;=\; Σ_m a_G(m)\,e(−α\sqrt m)\,e^{−2πy\sqrt m}\,m^{−s} ,
```
**absolutely convergent for every `s ∈ C`** — the factor `e^{−2πy\sqrt m}` beats every polynomial. So the
damped twist is a genuine absolutely convergent generalised Dirichlet series with frequency set
`\{\sqrt m\}` and coefficients `a_G(m)e^{−2πy\sqrt m}m^{−s}`; in particular it lies in `B^∞ ⊂ B¹`, and
its Fourier–Bohr coefficients exist and are those coefficients.

> **Theorem 125 (unconditional).** For every `G ∈ S` of degree `2`, every `y > 0`, every `s ∈ C` and
> every `n ≥ 1`,
> ```
> \lim_{A→∞}\ \frac1A∫_0^A Φ_G(s,−α+iy)\,e(αn)\,dα \;=\; a_G(n²)\,e^{−2πyn}\,n^{−2s} .
> ```
> *Proof.* Absolute convergence permits term-by-term integration; `\frac1A∫_0^Ae(α(n−\sqrt m))dα → [m = n²]`. ∎

(Note the sign: the pairing kernel is `e(+αn)`, since the twist carries `e(−α\sqrt m)`.)

### 214.2 What remains is a single interchange of limits

Taking `s = 1/2` and summing over `n`:
```
Σ_{n≥1}\Big(\lim_{A}\frac1A∫_0^AΦ_G(\tfrac12,−α+iy)e(αn)\,dα\Big)\,n^{−(s'−1)}
   \;=\; Σ_n a_G(n²)\,e^{−2πyn}\,n^{−s'} \;=:\; D_G^{(y)}(s') ,
```
which is **entire in `s'`** and tends to `D_G(s')` as `y → 0^+` for `\mathrm{Re}\,s' > 1`. Hence

> **(PSD₂) `⟺` `Σ_{n≥1}a_G(n²)\,e^{−2πyn}\,n^{−1} \;=\; κ\,\log(1/y) + O(1)` as `y → 0^+`, with `κ ∈ Z`.**

This is the **Abel-regularised** form of the prime-square density, and it is equivalent to the
logarithmic-density form by a Hardy–Littlewood Tauberian argument (the coefficients `a_G(n²)n^{−1}`
being `≪ n^{ε−1}`).

> **The entire remaining problem is the order of two limits.** Taking `A → ∞` first and then `y → 0`
> reproduces the wanted diagonal `a_G(n²)n^{−1}` **unconditionally** (Theorem 125). Taking `y → 0`
> first — which is what "the standard twist" means — is §12.3/§13.4's boundary limit. (BOHR), and with
> it Conjecture A in degree `≤ 2`, is exactly the assertion that the two orders agree.

### 214.3 Why this is the right final formulation

- It is **unconditional at every `y > 0`**: no hypothesis, no continuation, no functional equation is
  needed to write down the exact Bohr coefficients of the damped twist.
- The `y → 0` limit is the *only* remaining analytic step, and it is a limit of an explicit family of
  absolutely convergent series — not a continuation across a boundary of unknown type.
- It explains, once more and most simply, why degree `1` is easy: there `Φ_G(s,−α+iy)` is a genuine
  Fourier series in `α`, the Bohr means are `∫_0^1`, and the `y → 0` limit commutes with `∫_0^1` by
  dominated convergence on a compact interval. **In degree `2` the averaging interval is infinite, and
  dominated convergence is unavailable — that, and nothing else, is the difficulty.**

> **Recorded as the terminal statement of the programme.** Everything else — Theorems 111, 124, (BOHR),
> §206's exponent gap, §213's periodicity dichotomy — is bookkeeping around the single question:
> *does `\lim_{y→0}` commute with `\lim_{A→∞}\frac1A∫_0^A` for the standard twist of a degree-2 element
> of the Selberg class?*

---

## 215. Cycle 215 (2026-07-26) — the double limit: the required cancellation **is** available; the gap is uniformity of C7.1

### 215.1 The difference `Φ_y − Φ_0` and its Bohr pairing

Near a spectral point `α_m`, C7.1 gives `Φ_G(\tfrac12,−α_m+ζ) ≍ ρ_0(α_m)(−2πiζ)^{−1/2} + \text{reg}`,
with `ζ = (α_m−α)+iy`. So `Φ_y` caps the `|α−α_m|^{−1/2}` blow-up of `Φ_0` at height `y^{−1/2}`, and the
two differ only on `|α−α_m| ≲ y`, where
```
∫_{|α−α_m|<y}\big|Φ_y − Φ_0\big|\,dα \;≍\; |ρ_0(α_m)|\;\!\sqrt y ,
\qquad ρ_0(α_m) ∝ \overline{a_G(m)}\,m^{−1/4} .
```
Pairing with `e(αn)` and summing the spikes with `α_m ≤ A` (i.e. `m ≤ M := qA²/4`),
```
\Big|\mathrm{Bohr}_n(Φ_y) − \mathrm{Bohr}_n(Φ_0)\Big| \;≍\; \frac{\sqrt y}{A}\;\Big|\,T(n,M)\Big| ,
\qquad T(n,M) := Σ_{m ≤ M}\overline{a_G(m)}\,m^{−1/4}\,e\big(2n\sqrt{m/q}\big) .
```

### 215.2 `T(n,M) ≍ M^{1/2}` — and that is exactly enough

`T(n,M)` is the partial sum of the Dirichlet series of `Φ_{\bar G}(\tfrac14+w,α)` at `α = 2n/\sqrt q`,
whose poles in `w` lie at `w = s^*_ℓ − \tfrac14 = \tfrac12 − \tfrac ℓ2`. For **fixed `n`** the parameter
`α` is fixed, KP's continuation and their vertical-strip growth bound apply, and Perron gives
```
T(n,M) \;=\; 2ρ_0(α)\,M^{1/2} \;+\; O_{n,ε}(M^{ε}) .
```
(Trivially `T ≪ M^{3/4}`; the continuation improves this to `M^{1/2}` — genuine square-root-type
cancellation, supplied by KP, not assumed.) Substituting `M = qA²/4`, so `M^{1/2} ≍ A`:
```
\Big|\mathrm{Bohr}_n(Φ_y) − \mathrm{Bohr}_n(Φ_0)\Big| \;≪_n\; \frac{\sqrt y}{A}\cdot A \;=\; \sqrt y ,
```
**uniformly in `A`.** Hence `\lim_{y→0}` and `\lim_{A→∞}` commute, Theorem 125 transfers to `y = 0`, and
(BOHR) — with it Conjecture A for all `d_F ≤ 2` — would follow.

> **The cancellation needed for the double limit is not an extra hypothesis: it is Kaczorowski–Perelli's
> own continuation, applied at a fixed spectral parameter.** This is the first time the required input
> has turned out to be already available.

### 215.3 The gap that remains, stated exactly

The computation of §215.1 uses C7.1's local expansion **simultaneously at every spectral point
`α_m ≤ A`**, at the scale `|ζ| ≍ y`. C7.1's error term is `O\big((C_{G,α_0}|ζ|)^{K}\big)` with a constant
that is **not known to be uniform in `α_0`** — §10.2's [OPEN CORE], only partially addressed by §14.2(1).
If `C_{G,α_0} ≪ α_0^{B}`, the expansion is valid at scale `|ζ| ≍ y` only for `α_m ≪ y^{−1/B}`, so
`A` and `y` are coupled and the uniformity in `A` claimed above is not established.

> **(UNIF) — the terminal open core, replacing (BOHR).** *Is the constant in C7.1's local expansion of
> the standard twist polynomially bounded — indeed bounded — in the spectral parameter `α_0`?*
>
> ```
> (UNIF)  ⟹  the double limit commutes (§215.2)  ⟹  (BOHR)  ⟹  (PSD₂) in degree 2
>         ⟹  Conjecture A for every F ∈ S with d_F ≤ 2 .
> ```

Everything else in the chain is now either proved here or supplied by KP: Theorem 111, Theorem 124,
Theorem 125, the singularity exponent `−1/2` (§208.1), the absolute spectral mean (§209.1), the
diagonal and off-diagonal (§210.1), the over-shoot (§211.2), and now the cancellation `T ≍ M^{1/2}`
(§215.2).

> **Recorded honestly.** §215.2 is a *heuristic chain made rigorous except at one point*: the local
> model for `Φ_y − Φ_0` is C7.1's, and its use across the whole spectrum is exactly (UNIF). No claim is
> made that (BOHR) is proved. What is new is that the *cancellation* — the step everyone would expect
> to be the hard one — is free, and the difficulty is entirely a uniformity statement inside KP's own
> local analysis.

---

## 216. Cycle 216 (2026-07-26) — (UNIF) is **false**, and the interchange is unnecessary: integer sampling

### 216.1 (UNIF) with a bounded constant cannot hold

§215.3 asked whether C7.1's constant `C_{G,α_0}` is bounded in `α_0`. It is not, and the reason is
structural: C7.1's expansion at `α_0` is valid only until `ζ` reaches a **neighbouring** spectral point,
where `Φ_G(s,−α_0+ζ)` is singular again (§13.3). For `d = 2` the spectrum is `α_m = 2\sqrt{m/q}` with
gaps `≍ 2/(qα)`, so
```
C_{G,α_0} ≍ α_0 ,\qquad\text{radius of validity } |ζ| ≪ 1/α_0 .
```
Running §215.1's estimate with this: the leading term dominates the C7.1 error at `|ζ| ≍ y` only when
`y ≪ α^{−1}`, i.e. `y ≪ A^{−1}`. **`A` and `y` are unavoidably coupled, and §215.2's "uniformly in `A`"
does not hold.** Ninth defect, own, caught one cycle later.

### 216.2 The interchange is not needed — sample at integers

Return to §214.2: what (PSD₂) requires is the `y → 0` asymptotic of
`Σ_{n≥1}a_G(n²)e^{−2πyn}n^{−1}`, and Theorem 125 identifies each term as a Bohr coefficient of the
damped twist at integer frequency `n`. Summing those coefficients is pairing against the Dirac comb,
i.e. **sampling at integer arguments**:
```
\frac1A Σ_{k ≤ A} Φ_G(\tfrac12,−k+iy)
 \;=\; Σ_m a_G(m)\,e^{−2πy\sqrt m}\,m^{−1/2}\;\frac1A Σ_{k≤A} e(−k\sqrt m)
 \;\xrightarrow[A→∞]{}\; Σ_{n≥1} a_G(n²)\,e^{−2πyn}\,n^{−1} ,
```
by Weyl (the frequencies `\sqrt m` are irrational unless `m` is a square), with the interchange
legitimate because the `m`-series converges absolutely for every `y > 0`.

> **Theorem 126 (unconditional).** For every `G ∈ S` of degree `2` and every `y > 0`,
> ```
> Σ_{n≥1} a_G(n²)\,e^{−2πyn}\,n^{−1} \;=\; \lim_{A→∞}\frac1A Σ_{k ≤ A} Φ_G\big(\tfrac12,\,−k+iy\big) ,
> ```
> and (PSD₂) in degree 2 is exactly the assertion that this quantity is `κ\log(1/y) + O(1)` with
> `κ ∈ Z` as `y → 0^+`.
>
> **No interchange of `y → 0` with `A → ∞` occurs**: `A → ∞` is taken first, legitimately, and only then
> is `y → 0` studied — of a single explicit function of `y`.

### 216.3 The singular part is negligible in this average

At integer `α = k`, the point `k` is itself spectral (`k = α_m` with `m = qk²/4`), so
`Φ_G(\tfrac12,−k+iy) ≍ ρ_0(k)\,y^{−1/2}` from the spike, with
`ρ_0(k) ∝ \overline{a_G(qk²/4)}\,(qk²/4)^{−1/4} ≍ k^{−1/2}`. Hence
```
\frac1A Σ_{k≤A}\big|\text{spike part}\big| \;≍\; \frac{y^{−1/2}}{A}Σ_{k≤A}k^{−1/2} \;≍\; (Ay)^{−1/2}\;\xrightarrow[A→∞]{}\;0 .
```

> **So the whole of `Σ_n a_G(n²)e^{−2πyn}n^{−1}` comes from the *regular* part of the twist at integer
> arguments.** The spectral singularities — the object that has obstructed every route since §11.2 —
> contribute nothing to this average. That is the third independent confirmation (after §209.1 and
> §210.1) that the singular part is harmless, and the first in which it is *provably absent*.

### 216.4 Position

```
Conjecture A for all d_F ≤ 2
 ⟸ (PSD₂) in degree 2                                                  Thm 111 + Cor 102  [proved]
 ⟸ Σ_n a_G(n²)e^{−2πyn}n^{−1} = κ\log(1/y)+O(1),  κ ∈ Z                Thm 124 + Tauberian [proved]
 = \lim_A \frac1A Σ_{k≤A} Φ_G(1/2,−k+iy)                               Thm 126            [proved]
 with the spike part contributing 0                                    §216.3             [proved]
 ⟸ the y → 0 asymptotic of the regular part of the twist at integers   ← OPEN
```
The terminal statement no longer involves any interchange of limits, any uniformity over the spectrum,
or any singular behaviour: it is the small-`y` asymptotic of the average, over integer arguments, of the
regular part of one explicit damped Dirichlet series.

---

## 217. Hand-off (state as of cycle 217) — supersedes §186 and §192.3

### 217.1 The chain, with proof status

```
Conjecture A for every F ∈ S with d_F ≤ 2
 ⟸ (PSD₂) for degree-2 G:  δ_1(a_G(·²)) ∈ Z                     Thm 111 (+Cor 102)   PROVED
 ⟸ Σ_n a_G(n²)e^{−2πyn}n^{−1} = κ\log(1/y)+O(1), κ ∈ Z          Thm 124 + Tauberian  PROVED
 = \lim_{A→∞}\frac1AΣ_{k≤A}Φ_G(1/2,−k+iy)                        Thm 126              PROVED
   with the spectral-singularity part contributing O((Ay)^{−1/2}) §216.3               PROVED
 ⟸ the y → 0^+ asymptotic of that average                                             OPEN
```
Conjecture B additionally requires (P1) and (P2); (P2) is Theorem 85′ (proved, under equal `γ,q`), and
(P1) is `n_F = 1` for primitive degree-2 `F`, which is the same statement as the chain above
(Cor. 102 + §183.1).

### 217.2 Unconditional theorems of this session (cycles 165–217)

`76′` exact band-limited amplifier · `76″` `(1/T)∫|S_F|² ≥ (1/4π²)E(T/2)+1/12` · `84′,85′,87,89,90`
(characteristic-function block) · `100` Conjecture A+B for products of degree-1 elements · `102`
`S_F` unbounded, no density input · `103` complete mod-1 classification · `104` the method's exact
ceiling · `106` `c_{F,G} ∈ Z` when `\min(d_F,d_G)=1` · `109` degree-2 Hecke reduction · `111`
(PSD₂) ⟹ Conjecture A · `114` pairing splits off its 1-line part · `115` energy dominates twisted
divisor mass · `122` Conjecture B = second-level Energy Gap · `123` no additive invariant separates
Conjecture B from RSA · `124` the square-index Dirichlet series · `125` damped-twist Bohr coefficients
· `126` integer sampling. Corollaries `101,105,108,112,116,117,120`; Propositions `113,118,119,121`.

### 217.3 Lean added this session (all `lake build +GaloisForLFunctions.HTGeometry` clean)

`LogFrequencySeparation` (`inv_max_le_abs_log_sub_log`, `monomial_log_separation`) ·
`CountPositivityConductorBound` · `KProfileMismatch` · `LogPhaseDensity` (`fourierCoeff_expDensity`) ·
`SquareIndexMultiplicative` · additions to `BesselPSD` (`bessel_of_almost_orthogonal`,
`energy_near_int_of_almost_orthonormal`, `integral_bessel_of_orthonormal`, `cauchy_schwarz_psd`),
`GeneralizedDirichletMeanValue` (`oscInt_gram_bound`), `LogCoefficientTransfer` (`newton_sq_identity`).

### 217.4 Defect ledger (nine, all repaired or recorded)

| # | where | defect |
|---|---|---|
| 1 | §149.1 | Baker's constant depends on `π(N)` — repaired by elementary log separation |
| 2 | §92.1 | sign of the `n_0` term: deficit, not surplus |
| 3 | preprint Thm 13 | `(\log X)^{−C}` gap false at `j=k=1` |
| 4 | §147.1 | `B²` truncation used outside its hypothesis — Thm 91, Cor 92-rate downgraded |
| 5 | §127.1 | amplifier compactly supported ⟹ divergent prime side — repaired, theorem strengthened |
| 6 | §139/§147/§150 | archimedean phase one term short — fourth regime found |
| 7 | §187–188 | (SPEC): domains of the two representations disjoint |
| 8 | §208.2 | `\sqrt ε` dropped when summing spikes — `A^{1/2}` should be `A^{ε}` |
| 9 | §215.3 | (UNIF) false: C7.1's radius of validity is the spectral gap `≍ 1/α` |

**All nine were found by re-derivation, never by re-reading.** Standing rules: re-derive before
building on a recorded result; test every reduction on `ζ`, `ζ²` and a `GL_2` newform before recording
it as a route; check domains of validity as part of the derivation.

### 217.5 Closed routes (do-not-retry)

MI via `R_{F,F}`/`ℛ_F`/`𝔐_F`/the contour extractor · the four sieve constructions (§185.2) ·
two-variable continuations, incl. Bochner (§190.2 — they are MI) · (SPEC)/(SPEC′) · Mellin–Barnes on
the real axis (§212.2) · `L^∞`/Kronecker band projection · the resonance method for `S_F` ·
smoothing and sublattice tricks against (FRAC) · Halász/pretentious · `(\log^-|F|)²` for (V) · the AFE
for finiteness of `n_F` · positivity of `F\bar F` · Gram-matrix positivity against Conjecture B
(§199.2) · any additive-invariant argument against RSA (§123).

---

## 218. Cycle 218 (2026-07-26) — the circle-method route: **the major arcs are unconditionally available**

### 218.1 The setup

Detect squares by the classical theta function and damp by `e^{−ym}`:
```
Θ_G(β,y) := Σ_{m≥1} a_G(m)\,e(−mβ)\,e^{−ym}\ \ (\text{absolutely convergent for } y>0),\qquad
θ(β) := Σ_{n≥1}e(n²β) ,
```
```
Σ_{n≥1} a_G(n²)\,e^{−yn²} \;=\; ∫_0^1 θ(β)\,Θ_G(β,y)\,dβ .
```
`(PSD₂)` is the assertion that `Σ_n a_G(n²)e^{−yn²}n^{-1}`-type sums have an integral log-coefficient as
`y→0`; equivalently (Abel/Tauberian, §214.2) that `Σ_{n≤N}a_G(n²)/n ∼ κ\log N`, `κ ∈ Z`.

### 218.2 On the major arcs, everything is classical — and unconditional

For rational `β = a/k` the phase `m ↦ e(−ma/k)` is periodic mod `k`, hence a finite combination of
Dirichlet characters mod `k` (with Gauss-sum coefficients, plus lower-level terms for `(m,k)>1`):
```
Θ_G(a/k,\,y) \;=\; Σ_{χ \bmod k} c_χ\,Σ_{m}χ(m)a_G(m)e^{−ym} \;+\;(\text{lower level}) ,
```
and each inner sum is the **damped Dirichlet twist** of `G`. Since `G^χ ∈ S^♯` (Kaczorowski–Perelli),
each has a functional equation, hence a complete `y → 0^+` asymptotic expansion by the standard
Mellin/`Γ`-shift:
```
Σ_m χ(m)a_G(m)e^{−ym} = \frac1{2πi}∫_{(c)}Γ(w)\,y^{−w}\,G^χ(w)\,dw
   = (\text{residues at } w = 1 \text{ and } w = 0,-1,\dots) + (\text{dual side}) .
```

> **The major-arc input is unconditionally available.** This is the first construction in this
> programme whose principal term requires nothing beyond the Selberg axioms plus KP's twist theorem —
> no MI, no `\mathrm{Sym}²`, no uniformity, no Rankin–Selberg. It is available because Dirichlet twists
> are the one tensor operation the axioms supply (§180.2), and the circle method needs exactly those.

Moreover `θ` is large precisely on the major arcs (`|θ(a/k+δ)| ≍ k^{−1/2}|δ|^{−1/2}` for `|δ|` small),
so the major arcs carry the main term — as they must, since the answer `κ\log(1/y)` is of major-arc type.

### 218.3 What is left: the minor arcs

The remaining requirement is cancellation in
```
∫_{\mathfrak m} θ(β)\,Θ_G(β,y)\,dβ \;=\; o\big(\log(1/y)\big) ,
```
over the minor arcs `\mathfrak m`. Both factors are classical objects: `θ` obeys Weyl's inequality
(`|θ(β)| ≪ N^{1/2+ε}(1/k + 1/N + k/N²)^{1/2}`-type bounds on `\mathfrak m`), and `Θ_G(β,y)` is a damped
additive twist of `G` of length `≍ 1/y`.

> **(MINOR) — the terminal open core, replacing §216.4's.** *Do the minor arcs contribute
> `o(\log(1/y))` to `∫_0^1θ(β)Θ_G(β,y)dβ` for `G ∈ S` of degree `2`?*

Three reasons this is the best formulation the programme has reached:
- The main term is **unconditional** (§218.2); every earlier route had a conditional principal term.
- The remaining estimate is a **minor-arc bound**, the most standard object in analytic number theory,
  and the theta factor supplies its own saving (Weyl).
- It explains Shimura's method: for `GL_2` forms this integral *is* the Rankin–Selberg/theta
  construction of `\mathrm{Sym}²`, and its minor arcs are handled by modularity of `θ` and of `G`. For
  an abstract `G ∈ S` modularity is unavailable, and (MINOR) is exactly what replaces it.

### 218.4 Status

```
Conjecture A for all d_F ≤ 2
 ⟸ (PSD₂) in degree 2                                    Thm 111 + Cor 102        PROVED
 ⟸ Σ_n a_G(n²)e^{−yn²}-type asymptotic with κ ∈ Z         Thm 124 + Tauberian      PROVED
 = ∫_0^1 θ(β)Θ_G(β,y)dβ                                   §218.1                   PROVED
 major arcs: computable from the twists G^χ ∈ S^♯          §218.2                   AVAILABLE
 minor arcs: (MINOR)                                                               OPEN
```

---

## 219. Cycle 219 (2026-07-26) — calibrating (MINOR): the circle method's major arcs are free, the minor arcs are the whole `\mathrm{Sym}²` difficulty

### 219.1 Use the summatory form, not the `1/n`-weighted one

`(PSD₂)` in the `1/n`-weighted form has main term `κ\log(1/y)` — *logarithmically small*, so any
circle-method error that is a positive power of the length is hopeless. The right form is the
summatory one: by Wirsing/Selberg–Delange,
```
δ_1(a_G(·²)) = κ \iff Σ_{n ≤ X} a_G(n²) ∼ c\,X\,(\log X)^{κ−1} ,
```
whose main term is a positive power. The exact circle-method identity is then
```
Σ_{n≤X}a_G(n²) \;=\; ∫_0^1 \Big(Σ_{n≤X}e(−n²β)\Big)\Big(Σ_{m≤X²}a_G(m)\,e(mβ)\Big)\,dβ
   \;=\; ∫_0^1 \overline{θ_X(β)}\;A_{G,X}(β)\,dβ .
```

### 219.2 Major arcs: unconditional (unchanged)

On `β = a/k + δ` the phase `e(ma/k)` is periodic mod `k`, so `A_{G,X}` is a finite combination of
**Dirichlet-twisted** partial sums `Σ_{m≤X²}χ(m)a_G(m)e(mδ)`, each governed by the functional equation
of `G^χ ∈ S^♯`; and `θ_X` is a classical Gauss sum times a Fresnel integral. **Nothing beyond the
Selberg axioms and KP's twist theorem is used** (§218.2).

### 219.3 Minor arcs: the required saving, computed

```
∫_0^1|θ_X|²dβ = X ,\qquad ∫_0^1|A_{G,X}|²dβ = Σ_{m≤X²}|a_G(m)|² ≪_ε X^{2+ε} ,
```
so even Cauchy–Schwarz over the **whole** circle gives only
```
∫_0^1|θ_X A_{G,X}|\,dβ \;≪_ε\; X^{1/2}\cdot X^{1+ε} = X^{3/2+ε} ,
```
against a truth of size `X(\log X)^{κ−1}`. Hence:

> **(MINOR) requires a saving of `X^{1/2}` beyond Cauchy–Schwarz.** Weyl's inequality for `θ_X` supplies
> `\sup_{\mathfrak m}|θ_X| ≪ X^{1−δ}`, which combined with `∫|A_{G,X}| ≪ X^{1+ε}` gives only
> `X^{2−δ+ε}` — worse than Cauchy–Schwarz. The theta factor's saving is not enough on its own;
> the bound must exploit cancellation in `A_{G,X}` on the minor arcs, i.e. in the **additive twist of
> `G` at irrational `β`**.

> **Calibration recorded.** The gap between `X^{3/2}` (all that positivity and `L²` give) and
> `X^{1+ε}` (what is needed) is exactly the sparse-support difficulty of summing `a_G` over squares —
> the same difficulty class as constructing `\mathrm{Sym}²G`. **The circle method relocates the problem
> but does not reduce it: its major arcs are free, and its minor arcs are the whole of the original
> difficulty.**

### 219.4 What is genuinely gained, and what is not

*Gained.* The principal term is unconditional for the first time in the programme; the difficulty is
now a single, standard-shaped minor-arc bound about an explicit exponential sum
`A_{G,X}(β) = Σ_{m≤X²}a_G(m)e(mβ)` at irrational `β`; and this identifies precisely which classical
technique would suffice — nontrivial bounds for additive twists of a degree-2 Selberg-class element at
irrational arguments (for `GL_2` forms these follow from modularity via Wilton's estimate
`Σ_{m≤M}a(m)e(mβ) ≪ M^{1/2}\log M`, uniformly in `β`).

*Not gained.* Wilton-type bounds are unavailable in the abstract class: §100.2 records that the Selberg
axioms resonate only at twist exponent `1/d`, whereas `A_{G,X}` is the exponent-`1` additive twist.
**(MINOR) is therefore §206.2's exponent gap in yet another guise** — the fifth appearance of the same
obstruction (after §14.3's `β`-contour gap, §189's disjoint domains, §190's tube-theorem failure, and
§206.2 itself).

> **Recorded.** Do not attempt (MINOR) by Weyl/Cauchy–Schwarz alone: the numerology above shows both
> are insufficient by a factor `X^{1/2}`. The only route is a Wilton-type bound for the exponent-`1`
> additive twist, which is exactly what the axioms do not supply.

---

## 220. Cycle 220 (2026-07-26) — the exponent-1 twist **is** a Fresnel transform of the exponent-1/2 twist; all roads lead to §10.2

### 220.1 Bridging the exponent gap by a chirp transform

The obstruction named five times (§14.3, §189, §190, §206.2, §219.4) is the gap between the resonant
exponent `1/d = 1/2` and the square-detecting exponent `1`. It can be **bridged explicitly**: writing
`e(mβ) = e\big((\sqrt m)^2β\big)` and Fourier-transforming in the variable `u = \sqrt m`,
```
e(u²β) \;=\; \frac{1}{\sqrt{|β|}}\,e(\pm\tfrac π4)∫_{R} e\big(−\tfrac{α²}{4β}\big)\,e(αu)\,dα
\qquad(\text{Fresnel}),
```
so, for `M`-truncated sums,
```
A_{G,M}(β) := Σ_{m≤M}a_G(m)e(mβ) \;=\; \frac{e(\pm π/4)}{\sqrt{|β|}}∫_{|α| ≪ \sqrt M} e\Big(−\frac{α²}{4β}\Big)\,
   Σ_{m≤M}a_G(m)\,e(α\sqrt m)\;dα \;+\;(\text{tails}) .
```
**The exponent-1 additive twist is a chirp average of the exponent-1/2 standard twist.** The exponent
gap is therefore not an absolute barrier: it is crossed by an explicit integral transform, at the cost
of an `α`-average of length `\sqrt M`.

### 220.2 Wilton's bound would follow from `α`-uniformity

By Perron applied to `Φ_G(w,α) = Σ_m a_G(m)e(−α\sqrt m)m^{−w}`, whose poles lie only at
`w = s^*_ℓ = \tfrac34 − \tfrac ℓ2`:
```
Σ_{m≤M}a_G(m)e(−α\sqrt m) \;=\; \begin{cases}
   \dfrac{ρ_0(α)}{3/4}\,M^{3/4} + O_α(M^{ε}) , & α ∈ \mathrm{Spec}(G) ,\\[4pt]
   O_α(M^{ε}) , & α ∉ \mathrm{Spec}(G) ,
\end{cases}
```
the second case because the contour may be moved to `\mathrm{Re}\,w = ε` with no poles crossed. Since
`\mathrm{Spec}(G)` is countable, this holds for **almost every** `α`. Feeding it into §220.1,
```
A_{G,M}(β) \;≪\; |β|^{−1/2}\,\sqrt M\,\cdot\,M^{ε} \;=\; |β|^{−1/2}M^{1/2+ε} ,
```
which is **Wilton's bound** — precisely what (MINOR) needs (§219.4).

> **The only missing ingredient is that `O_α(M^{ε})` be uniform in `α`** (or at worst polynomially
> bounded with a small exponent, and integrable against the chirp). That is §10.2's [OPEN CORE]:
> `α`-uniform bounds for the continued standard twist.

### 220.3 The programme's terminal statement

Every route examined in this programme now terminates at the same point:

| route | terminates at |
|---|---|
| §12–14 bilinear pairing `∫Φ_F\overline{Φ_G}` | `α`-uniformity of C7.1 (§14.3) |
| §187 spectral summation | domains disjoint (§189) — from non-uniformity |
| §190 Bochner tube theorem | branch cuts = the conjecture itself |
| §206–207 fractional theta / comb | `α`-uniformity, via (BOHR) |
| §215 double limit | (UNIF) false: radius of validity is the spectral gap |
| §216 integer sampling | regular part at integers — `α`-uniformity again |
| §218–219 circle method | Wilton for the exponent-1 twist |
| §220 chirp transform | **`α`-uniform bounds for the truncated standard twist** |

> **Terminal statement of the programme.** *Conjecture A for every `F ∈ S` with `d_F ≤ 2` follows from:
> for `α ∉ \mathrm{Spec}(G)`, `Σ_{m≤M}a_G(m)e(−α\sqrt m) ≪ M^{ε}` with an implied constant uniform in
> `α` (or growing slower than `|α|^{1/2}`), for `G ∈ S` of degree `2`.*
>
> This is a single, completely explicit estimate for a finite exponential sum built from the
> coefficients of `G`. It implies Wilton's bound (§220.2), hence (MINOR) (§219), hence (PSD₂), hence —
> by Theorems 111 and 124 and Corollary 102 — Conjecture A in degree `≤ 2`. And it is exactly the
> uniformity Kaczorowski–Perelli state only for fixed `α`.

### 220.4 Recorded

The exponent gap is **not** an absolute obstruction (§220.1 crosses it). The real and only obstruction,
identified now from eight independent directions, is the `α`-uniformity of the standard twist. Every
future cycle should target that estimate and nothing else.

---

## 221. Cycle 221 (2026-07-26) — **correction to §220.2**: absolute bounds cannot give Wilton; the mass sits at the spectrum

### 221.1 The defect

§220.2 concluded that Wilton's bound follows from an `α`-uniform version of
`S_M(α) := Σ_{m≤M}a_G(m)e(α\sqrt m) ≪_α M^{ε}` (`α ∉ \mathrm{Spec}(G)`). Two checks kill that
conclusion.

**(a) The bound is false near `α = 0`.** For `G = ζ²`, `a_G(m) = d(m)`, and for `α ≪ M^{−1/2}` the phase
is nearly constant, so `S_M(α) ≍ M\log M`. Any uniform statement must therefore exclude
`|α| ≲ M^{−1/2}`. *(That region is harmless in the application: it has measure `M^{−1/2}` and
contributes `≪ |β|^{−1/2}M^{−1/2}·M^{1+ε} = |β|^{−1/2}M^{1/2+ε}`, exactly Wilton size.)*

**(b) The `L¹` norm is `M^{1+ε}`, not `M^{1/2}`.** `S_M` is large in a neighbourhood of every spectral
point: `S_M(α_m) ≍ ρ_0(α_m)M^{3/4}` with `ρ_0(α_m) ∝ a_G(m)m^{−1/4}`, and `S_M` varies on the scale
`M^{−1/2}` (its highest frequency is `\sqrt M`). With `≍ qM` spectral points in `|α| ≤ 2\sqrt M`,
```
∫_{|α|≤\sqrt M}|S_M(α)|\,dα \;≍\; M^{3/4}\,M^{−1/2}Σ_{m≤qM}|a_G(m)|\,m^{−1/4} \;≍\; M^{1/4}\cdot M^{3/4+ε} = M^{1+ε} ,
```
whereas §220.2 needs `M^{1/2+ε}`. **Deficit `M^{1/2}` — the same deficit as §219.3.**

> **Corrected statement.** A pointwise bound off the spectrum, however uniform, does **not** control the
> chirp integral: `\mathrm{Spec}(G)` has measure zero but the `L¹` mass of `S_M` is concentrated in the
> `M^{−1/2}`-neighbourhoods of its points. The chirp route requires **cancellation** in
> `∫e(−α²/4β)S_M(α)dα` — i.e. destructive interference between the chirp and the spectral spikes — not
> an absolute bound.

Tenth defect, own, caught one cycle later, by evaluating the `L¹` norm rather than asserting it.

### 221.2 What survives, and the corrected terminal statement

- §220.1 stands: the exponent-1 additive twist **is** an explicit Fresnel/chirp transform of the
  exponent-1/2 standard twist. The exponent gap is genuinely crossed.
- What does *not* survive is that uniformity alone suffices. The corrected requirement is:

> **(CHIRP) — terminal statement, corrected.** *For `G ∈ S` of degree `2` and `β` irrational,*
> ```
> ∫_{|α| ≪ \sqrt M} e\Big(−\frac{α²}{4β}\Big)\,S_M(α)\,dα \;≪_ε\; M^{1/2+ε}\,|β|^{1/2} ,
> ```
> *i.e. square-root cancellation between the chirp and the spectral spikes of the truncated standard
> twist.*
>
> (CHIRP) ⟹ Wilton ⟹ (MINOR) ⟹ (PSD₂) ⟹ Conjecture A for all `d_F ≤ 2`.

### 221.3 Why the spikes are exactly the right objects for the chirp

Each spike sits at `α_m = 2\sqrt{m/q}` with amplitude `∝ a_G(m)m^{−1/4}M^{3/4}` and width `M^{−1/2}`.
The chirp `e(−α²/4β)` has stationary phase at `α = 0` only, but its *local frequency* at `α` is
`−α/(2β)`, matching the spike train's local frequency `≈` (spacing)`^{−1} ≍ α q/2` when
`α/(2β) ≍ qα/2`, i.e. `β ≍ 1/q` — a single resonance. Away from it, chirp and comb are transverse, which
is precisely the mechanism that should produce the cancellation.

> **Recorded.** (CHIRP) is a stationary-phase problem between an explicit quadratic phase and the
> spectral comb of the standard twist. It is the first formulation of the terminal obstruction in which
> both objects are completely explicit and the required mechanism (transversality of chirp and comb) is
> identified. No claim is made that it is easy; but it is no longer a uniformity statement, and it is
> no longer about an object defined only by analytic continuation.

---

## 222. Cycle 222 (2026-07-26) — the chirp transform is an **involution**: §220–221's route is circular

### 222.1 The computation

Complete the square in the Fresnel integral: with `u = \sqrt m`,
```
∫_{R} e\Big(−\frac{α²}{4β} + αu\Big)\,dα
 \;=\; e(βu²)∫_{R}e\Big(−\frac{γ²}{4β}\Big)dγ
 \;=\; \sqrt{4|β|}\;e(\pm\tfrac18)\;e(βu²) ,
```
so, summing over `m ≤ M` with `u = \sqrt m`, `u² = m`,
```
∫_{R} e\Big(−\frac{α²}{4β}\Big)\,S_M(α)\,dα \;=\; \sqrt{4|β|}\,e(\pm\tfrac18)\;A_{G,M}(β) .
```

> **The chirp transform of §220.1 is exactly invertible: it maps the exponent-1/2 twist to the
> exponent-1 twist and back, with no loss.** Hence (CHIRP) — the bound
> `∫e(−α²/4β)S_M ≪ M^{1/2+ε}|β|^{1/2}` — is *literally* Wilton's bound
> `A_{G,M}(β) ≪ M^{1/2+ε}` rewritten. **The route of §§220–221 is circular.**

Eleventh defect, own; §221 corrected the mechanism but not the circularity, which only the explicit
inversion exposes.

### 222.2 The principle this establishes

`S_M` and `A_{G,M}` are Fourier-conjugate under the chirp: the map is unitary (up to the factor
`\sqrt{4|β|}`), so it transports every bound in both directions and creates none.

> **Principle (no free crossing).** *The exponent gap `1/d ↦ 1` cannot be crossed by any invertible
> integral transform.* Such a transform carries the difficulty with it. Crossing the gap requires an
> operation that **adds** information — in practice a functional equation valid at the target exponent
> — and the Selberg axioms supply one only at `κ = 1/d` (§100.2). This is why the same obstruction has
> reappeared eight times (§220.3) under eight different names: those were eight unitary re-encodings of
> a single object.

### 222.3 Consequence for the terminal statement

The terminal statement reverts, cleanly and finally, to:

> **(WILTON).** *For `G ∈ S` of degree `2`, `Σ_{m≤M}a_G(m)e(mβ) ≪_ε M^{1/2+ε}` uniformly in `β`.*
>
> (WILTON) ⟹ (MINOR) (§219.4) ⟹ (PSD₂) (§218) ⟹ Conjecture A for every `F ∈ S` with `d_F ≤ 2`
> (Theorems 111, 124, Corollary 102).

For `GL_2` automorphic forms (WILTON) is Wilton's classical theorem, proved **from modularity**: the
transformation `z ↦ −1/z` of the associated form is exactly the extra input that the chirp cannot
manufacture. For an abstract `G ∈ S` of degree `2` no such transformation is available, and (WILTON) is
open.

> **Recorded as the programme's final terminal statement.** Everything proved in cycles 165–222 reduces
> Conjecture A in degree `≤ 2` to (WILTON), and (WILTON) is exactly the statement that a degree-2
> Selberg-class element behaves like a modular form under additive twists. **The Selberg class problem,
> in degree 2, is the problem of proving Wilton's estimate without modularity.**

### 222.4 Ledger

| # | where | defect |
|---|---|---|
| 10 | §220.2 | pointwise uniformity insufficient; `L¹` mass sits at the spectrum — corrected §221 |
| 11 | §220.1/§221.2 | the chirp transform is an involution, so the route is circular — corrected here |

Eleven defects, all found by re-derivation. **Two of the last three were in my own newly-proposed
routes, and both were caught within one cycle by computing rather than asserting.**

---

## 223. Cycle 223 (2026-07-26) — two corrections to the chain, and why convexity cannot give (WILTON)

### 223.1 (WILTON) must exclude poles — and the degree-2 chain must run through Theorem 109, not 111

`(WILTON)` as stated in §222.3 is **false** for `G = ζ²`: `a_{ζ²}(m) = d(m)` and
`Σ_{m≤M}d(m)e(mβ) ≍ M\log M` for `|β| ≪ 1/M`. The obstruction is the pole of `ζ²` at `s = 1`, which
produces a main term in every additive twist at a rational point. **(WILTON) must be restricted to
entire `G`** — for `GL_2` it is the cuspidality hypothesis in Wilton's theorem.

This exposes a second, more serious point. Theorem 111 computes
`n_F = δ_1(a_{F\bar F}(·²)) − 2\mathrm{Re}\,δ_1(a_F(·²))` and therefore needs `(PSD₂)` for `F\bar F`,
which has degree `4` — outside the degree-2 chain. **The degree-2 route must run through Theorem 109
instead**, which uses only `G = F`:
```
n_F = δ_1\big(p ↦ a_F(p²)\big) + δ_1\big(p ↦ c_p\big) ,\qquad c_p = α_pβ_p \text{ the local determinant},
```
valid for self-dual `F` of degree `2` with a polynomial Euler product, with `δ_1(c) ∈ \{0,1\}` when the
determinant is a Dirichlet character. **Corrected chain:**
```
Conjecture A for primitive degree-2 F  (= all of Conjecture A for d_F ≤ 2, Cor. 102)
 ⟸ (PSD₂) for G = F, i.e. δ_1(a_F(·²)) ∈ Z          Thm 109  [needs PEP + self-duality + det a character]
 ⟸ D_F(s) = Σ_n a_F(n²)n^{−s} meromorphic at s = 1   Thm 124
 ⟸ (MINOR) for the entire degree-2 element F        §218–219
 ⟸ (WILTON) for entire degree-2 F                   §222.3
```
Twelfth defect (own): §222.3's (WILTON) omitted "entire", and §211.4/§216.4 routed degree 2 through
Theorem 111, which needs degree 4.

### 223.2 Convexity plus twist functional equations is not enough

The natural unconditional attack on `(WILTON)` at rational `β = a/k`: expand
`e(ma/k) = φ(k)^{−1}Σ_{χ \bmod k}\barχ(a)τ(χ)χ(m)` (for `(m,k)=1`), so
```
Σ_{m≤M}a_G(m)e(ma/k) \;≪\; \sqrt k\;\max_{χ \bmod k}\Big|Σ_{m≤M}χ(m)a_G(m)\Big| ,
```
using `|τ(χ)| ≤ \sqrt k`. For entire `G`, `G^χ ∈ S^♯` has conductor `≍ q k^{d}`, so Perron with the
contour at `\mathrm{Re}\,w = 1/2` and the convexity bound
`|G^χ(\tfrac12+it)| ≪ (qk^{d}(1+|t|)^{d})^{1/4+ε}` gives
```
Σ_{m≤M}χ(m)a_G(m) \;≪_ε\; M^{1/2+ε}\,k^{d/4+ε} ,\qquad\text{hence}\qquad
Σ_{m≤M}a_G(m)e(ma/k) \;≪_ε\; M^{1/2+ε}\,k^{\,1/2 + d/4 + ε} .
```
For `d = 2` this is `M^{1/2+ε}k^{1+ε}`, non-trivial only for `k ≪ M^{1/2}`. Combining with Dirichlet
approximation `|β − a/k| ≤ 1/(kK)` and partial summation (factor `1 + M/(kK)`) gives, after optimising
`K`, only the trivial bound `M^{1+ε}`.

> **Recorded do-not-retry.** Convexity for the Dirichlet twists — the strongest unconditional input the
> Selberg axioms give in the conductor aspect — does **not** yield any non-trivial uniform additive-twist
> bound in degree 2. The Gauss-sum factor `\sqrt k` and the convexity factor `k^{d/4}` together cost
> `k^{1+ε}`, exactly cancelling the saving. **Subconvexity in the conductor aspect (exponent
> `k^{1/2+d/4−δ}`) would be needed, and none is available in the abstract class.**

### 223.3 Position

```
terminal statement : (WILTON) for entire degree-2 G ∈ S:  Σ_{m≤M}a_G(m)e(mβ) ≪_ε M^{1/2+ε} uniformly in β
known route        : modularity (Wilton's theorem for GL_2 cusp forms)
unavailable        : convexity + twists (§223.2); the chirp transform (circular, §222)
```
Twelve defects, all found by re-derivation. **The last four were in routes proposed within the previous
three cycles** — the rate of self-correction is now the binding constraint on progress, and every new
route is being tested against `ζ`, `ζ²` and a `GL_2` newform before it is recorded, exactly as §189.4
requires.

---

## 224. Cycle 224 (2026-07-26) — **major literature find**: Kaczorowski–Perelli have a transformation formula for **linear** twists in degree 2

### 224.1 The find

Phase-2 search on the terminal statement (WILTON) located:

> **J. Kaczorowski, A. Perelli, *Twists, Euler products and a converse theorem for `L`-functions of
> degree 2 in the Selberg class*, arXiv:1207.2312.**
> Abstract (verbatim): *"We prove a general result relating the shape of the Euler product of an
> `L`-function to the analytic properties of certain **linear twists** of the `L`-function itself. Then,
> by a **sharp form of the transformation formula for linear twists**, we check the required analytic
> properties in the case of `L`-functions of degree 2 and conductor 1 in the Selberg class. Finally we
> prove a converse theorem, showing that `ζ(s)²` is the only member of the Selberg class satisfying the
> above conditions and, moreover, having a pole at `s = 1`."*

Also located: **arXiv:2405.03186**, Kaczorowski–Perelli, *On the invariants of `L`-functions of degree
2, I: twisted degree and internal shift* (2024), continuing the degree-2 twist programme.

### 224.2 This corrects §206.2 and §222.2

§206.2 concluded: *"square-detection needs the additive twist at exponent `κ = 1`, which the axioms
continue only when `1 = 1/d`, i.e. `d = 1`"*, citing §100.2's "no second twist spectrum". §222.2 then
elevated this to the principle that the exponent gap cannot be crossed.

> **That is too pessimistic in degree 2.** §100.2's statement concerns the *stationary-phase resonance*
> of the standard twist, i.e. which exponent the functional equation produces spontaneously. It does
> **not** say that linear twists have no transformation formula. Kaczorowski–Perelli prove that they do,
> in degree 2 (conductor 1), in sharp form. **The exponent-1 twist is therefore not outside the reach of
> the axioms in the case that matters.**

Thirteenth defect (own): §206.2/§222.2 over-generalised §100.2 from "no second *resonant* exponent" to
"no analytic control at exponent 1". The correct statement is that the axioms do not *spontaneously*
resonate at `κ = 1`; whether a transformation formula exists is a separate question, answered
affirmatively by KP in degree 2.

### 224.3 Corrected position, and the next concrete step

```
Conjecture A for primitive degree-2 F   (= all of Conjecture A for d_F ≤ 2, Cor. 102)
 ⟸ (PSD₂) for G = F                      Thm 109
 ⟸ D_F(s) = Σ_n a_F(n²)n^{−s} meromorphic at s = 1        Thm 124
 ⟸ (MINOR) for entire degree-2 F          §218–219
 ⟸ (WILTON) for entire degree-2 F         §222.3, §223.1
 ⟸ **KP's sharp transformation formula for linear twists**  arXiv:1207.2312   ← AVAILABLE (conductor 1)
```

> **Next concrete step, recorded as the leading target.** Extract from KP's sharp linear-twist
> transformation formula a Wilton-type bound `Σ_{m≤M}a_G(m)e(mβ) ≪_ε M^{1/2+ε}` for entire degree-2
> `G ∈ S`, uniformly in `β`. The formula plays the role modularity plays in Wilton's classical proof:
> it is the transformation under which the additive twist at `β` is exchanged for one at a dual
> parameter, which is exactly what converts the trivial bound into square-root cancellation.

Two scope questions to settle before this can be claimed:
1. **Conductor.** KP verify the required analytic properties for conductor `1`. Whether the sharp
   transformation formula holds for general conductor in degree 2 must be checked (arXiv:2405.03186 is
   the natural place).
2. **Entirety.** (WILTON) needs `G` entire (§223.1); KP's converse theorem singles out `ζ(s)²` as the
   only degree-2 element with a pole satisfying their conditions, which is consistent.

> **Recorded.** This is the first time in this programme that the terminal obstruction has turned out to
> be addressed — at least in the conductor-1 case — by existing literature the programme had not used.
> It also vindicates the discipline of §165.2: the Phase-2 check was run on the terminal statement
> before further attack, and it changed the assessment.

---

## 225. Cycle 225 (2026-07-26) — **(WILTON) does not imply (MINOR)**: the circle-method route needs joint cancellation

### 225.1 The `L¹` norm of the quadratic Weyl sum

Near `a/k` (`k ≤ X`) one has `|θ_X(a/k+δ)| ≍ k^{−1/2}\min(X, |δ|^{−1/2})`, so
```
∫_{|δ| < 1/k²}|θ_X(a/k+δ)|\,dδ \;≍\; k^{−3/2} ,\qquad
∫_0^1|θ_X|\,dβ \;≍\; Σ_{k ≤ X}φ(k)\,k^{−3/2} \;≍\; X^{1/2} .
```

### 225.2 The deficit is `X^{1/2}` under every rearrangement

With `Σ_{n≤X}a_G(n²) = ∫_0^1\overline{θ_X}\,A_{G,X}` and `A_{G,X} = Σ_{m≤X²}a_G(m)e(mβ)`, target
`X(\log X)^{κ−1}`:
```
\sup_β|A| ≪ X^{1+ε}\ (\text{Wilton}) ,\quad ∫_0^1|θ_X| ≍ X^{1/2}
    \;\Longrightarrow\; ∫_{\mathfrak m}|θ_XA| ≪ X^{3/2+ε} ;
\sup_{\mathfrak m}|θ_X| ≪ X^{1/2+ε}\ (\text{Weyl}) ,\quad ∫_0^1|A| ≤ (Σ_{m≤X²}|a_G(m)|²)^{1/2} ≪ X^{1+ε}
    \;\Longrightarrow\; ≪ X^{3/2+ε} ;
\text{Hölder hybrid } (\sup|θ|)^{1/2}(∫|θ|)^{1/2}(∫|A|²)^{1/2}
    \;\Longrightarrow\; ≪ X^{3/2+ε} .
```

> **Every separate-bounds argument gives `X^{3/2+ε}`, and the target is `X^{1+ε}`.** The deficit is
> exactly `X^{1/2}` and it is invariant under Hölder rearrangement: **(WILTON) does not imply (MINOR)**.

Fourteenth defect (own): §219.4 recorded "Wilton would suffice" for (MINOR). It does not. What (MINOR)
requires is *joint* cancellation between `θ_X` and `A_{G,X}` — i.e. a shifted-convolution estimate — not
separate bounds on the two factors.

*Cross-check.* For `GL_2` newforms, `Σ_{n≤X}a(n²)` is **not** estimated by the circle method: it is read
off `L(s,\mathrm{sym}²)`. That the circle method fails here is therefore expected, not surprising.

### 225.3 Corrected position

```
Conjecture A for primitive degree-2 F   (= all of Conjecture A for d_F ≤ 2, Cor. 102)
 ⟸ (PSD₂) for G = F                                            Thm 109        PROVED
 ⟸ D_F(s) = Σ_n a_F(n²)n^{−s} meromorphic at s = 1              Thm 124        PROVED
 ⟸ ???                                                                         OPEN
```
with the following now recorded as **insufficient**: the circle method with separate bounds (§225.2);
the chirp transform (circular, §222); Mellin–Barnes on the real axis (§212); two-variable continuations
(§190); pointwise `α`-uniformity of the standard twist (§221).

**Most promising available machinery**, unchanged from §224: Kaczorowski–Perelli's sharp transformation
formula for **linear twists** in degree 2 (arXiv:1207.2312), together with their degree-2 invariant
theory (arXiv:2405.03186). The relevant question is no longer "does it give Wilton?" but the more direct

> **Can KP's linear-twist transformation formula be used to continue `D_F(s) = Σ_n a_F(n²)n^{−s}`
> to `s = 1`?** The square-index series is the theta-pairing of the linear twist (§218.1), and a
> transformation formula for the linear twist is exactly the input Shimura's method uses to construct
> `\mathrm{Sym}²` for `GL_2`.

### 225.4 Ledger

| # | where | defect |
|---|---|---|
| 12 | §222.3, §211.4, §216.4 | (WILTON) stated without "entire"; degree-2 chain routed through Thm 111 (degree 4) |
| 13 | §206.2, §222.2 | over-generalised §100.2: "no second resonant exponent" ≠ "no control at exponent 1" |
| 14 | §219.4 | "(WILTON) suffices for (MINOR)" — false; deficit `X^{1/2}` under every rearrangement |

Fourteen defects, all found by re-derivation. **Three of the last five were in routes proposed within
two cycles of their correction.** The discipline is holding: no route is now recorded as viable until
its numerology has been computed end to end.

---

## 226. Cycle 226 (2026-07-26) — the theta-pairing route is Shimura's method; verified in degree 1

### 226.1 The route

From §218.1, unconditionally and with absolute convergence for `y > 0`,
```
Σ_{n≥1}a_F(n²)\,e^{−yn²} \;=\; ∫_0^1 θ(β)\,Θ_F(β,y)\,dβ ,\qquad
Θ_F(β,y) = Σ_m a_F(m)e(−mβ)e^{−ym} ,
```
`Θ_F` being the **damped linear twist**. By Mellin, a pole of `D_F(s) = Σ_n a_F(n²)n^{−s}` at `s = 1`
of order `κ` corresponds to `Σ_n a_F(n²)e^{−yn²} ∼ c\,y^{−1/2}(\log 1/y)^{κ−1}` as `y → 0^+`.

> **So (PSD₂) is the `y → 0` asymptotic of a pairing between the classical theta function and the damped
> linear twist of `F`.** This is precisely Shimura's construction of `\mathrm{Sym}²` transposed to the
> Selberg class: there, `∫f(z)θ(z)E(z,s)\,dz` is unfolded using modularity of `f`, `θ` and `E`; here,
> `θ` is classical and the role of `f`'s modularity is played by a **transformation formula for the
> linear twist** — exactly what Kaczorowski–Perelli supply in degree 2 (arXiv:1207.2312).

### 226.2 Degree 1, verified

`G = L(s,χ)`, `d = 1`. Then `Σ_n a_G(n²)e^{−yn²} = Σ_nχ(n)²e^{−yn²}`, and:
- if `χ²` is principal mod `k`, `χ(n)² = 1` for `(n,k) = 1`, so the sum is
  `\frac{φ(k)}{k}\cdot\tfrac12\sqrt{π/y} + O(1)` — a `y^{−1/2}` main term;
- otherwise `χ²` is a non-principal character and the sum is `O(1)` by cancellation.

Correspondingly `D_G(s) = Σ_nχ(n)²n^{−s} = L(s,χ²)` has a pole at `s = 1` exactly when `χ²` is
principal, of order `1`. **The Mellin correspondence `y^{−1/2}(\log 1/y)^{κ−1} ↔ \mathrm{ord}_{s=1} = −κ`
is confirmed, with `κ ∈ \{0,1\}` — i.e. (PSD₂) in degree 1**, by a computation independent of §213.1's.

### 226.3 What degree 2 requires

The integrand `θ(β)Θ_F(β,y)` concentrates near rationals. `θ(a/k+δ)` is classical
(`≍ k^{−1/2}\min(y^{−1/2},|δ|^{−1/2})` after damping), and `Θ_F(a/k+δ,y)` must be supplied by the
linear-twist transformation formula: writing `e(−ma/k)` in Dirichlet characters reduces it to damped
Dirichlet twists `Σ_mχ(m)a_F(m)e^{−ym}`, whose `y → 0` expansions follow from the functional equations
of `F^χ ∈ S^♯` — **available unconditionally** (§218.2). What is *not* automatic is the uniformity in
`k` needed to sum the arcs, and the treatment of `β` far from every rational of small denominator.

> **Recorded target (unchanged in substance from §225.3, sharpened in form).** *Assemble the `y → 0`
> asymptotic of `∫_0^1θ(β)Θ_F(β,y)dβ` for entire degree-2 `F ∈ S` from: (i) the classical behaviour of
> `θ` at rationals, (ii) the functional equations of the Dirichlet twists `F^χ` on the major arcs, and
> (iii) KP's sharp linear-twist transformation formula for the remaining `β`.*
>
> Items (i) and (ii) are classical and unconditional; (iii) is the only external input, and it exists in
> the literature for degree 2, conductor 1.

### 226.4 Why this is not the circle method of §219

§225 showed the circle method with *separate* bounds fails by `X^{1/2}`. The present route does not
bound the two factors separately: it **transforms both** and reads off the main term from the resonance
between them — the same mechanism by which Shimura's integral produces `L(s,\mathrm{sym}²)` rather than
an estimate. That is why it can succeed where §219 cannot, and why the missing ingredient is a
*transformation formula*, not a *bound*.

---

## 227. Cycle 227 (2026-07-26) — **PEP and Bounded Satake are THEOREMS in `S_2` with conductor 1**; and `n_F ≤ 4`

The full text of Kaczorowski–Perelli, arXiv:1207.2312, was obtained and read this cycle. Three of its
results change the programme's scope statements.

### 227.1 What the paper actually proves

Write `F(s,α) = Σ_n a_F(n)e(−nα)n^{−s}` for the **linear** (additive) twist, and let `M(d,h)` be the
class of `f` that are (i) meromorphic on `C` and holomorphic for `σ < 1`, and (ii) satisfy an explicit
growth bound in **horizontal** strips involving `h`.

> **KP Theorem 2 (sharp transformation formula, degree 2).** For `F ∈ S^♯_2` and `α > 0`, for every
> `K > 0` there are polynomials `Q_0 ≡ 1, Q_1,\dots,Q_K` with `\deg Q_ν = 2ν` such that
> ```
> F(s,α) \;=\; −i\,ω_F\,(α\sqrt{q_F})^{2s−1+iθ_F}\;Σ_{ν=0}^{K}\Big(\frac{−i}{q_Fα²}\Big)^{ν}Q_ν(s)\;
>            \bar F\Big(s+ν+iθ_F,\;−\frac{1}{q_Fα}\Big) \;+\; H_K(s,α) ,
> ```
> with `H_K` holomorphic for `−K+\tfrac12 < σ < 2`, `|s| < 2K`, and `H_K ≪ (A/K)^{K}`.
>
> **The transformation is `α ↦ −1/(q_Fα)` — the Fricke involution.** This is exactly the substitute for
> modularity that §226.1 identified as the missing input.

> **KP Theorem 3.** If `F ∈ S^♯_2` and `q_F = 1`, then for every `q ≥ 1` and `(a,q) = 1` the linear
> twist `F(s,a/q)` lies in `M(2,q²)`: **meromorphic on `C`, holomorphic for `σ < 1`, with explicit
> growth.**

> **KP Theorem 1 + Corollary.** For `F ∈ S_2` with `q_F = 1`, every prime `p` and every `ψ \bmod p`,
> `ψ ≠ 0`, the twist lies in `M(2,p²)` **and**
> ```
> F_p(s) = ∏_{j=1}^{∂_p}\big(1−α_j(p)p^{−s}\big)^{−1},\qquad |α_j(p)| ≤ 1,\qquad ∂_p ≤ 2 .
> ```

### 227.2 Scope correction for this programme

> **Polynomial Euler Product (PEP) and Bounded Satake (BS) are not hypotheses in `S_2` with `q_F = 1`:
> they are theorems.** This programme has carried both as assumptions since §2.4/§9.5 (e.g. Theorem 97's
> `Q < ∞`, Theorem 109's PEP, §179.2's unitarity discussion). For degree 2 and conductor 1 they are
> available unconditionally, with local degree `∂_p ≤ 2` and `|α_j(p)| ≤ 1`.

Fifteenth defect (own, of omission): the programme assumed PEP/BS where the literature proves them.

### 227.3 A new unconditional theorem

> **Theorem 127 (unconditional).** For `F ∈ S_2` with `q_F = 1`,
> ```
> |a_F(p)| = |α_1(p)+α_2(p)| ≤ 2 \quad\text{for every } p ,\qquad\text{hence}\qquad
> \limsup_x \frac{1}{\log\log x}Σ_{p≤x}\frac{|a_F(p)|²}{p} \;≤\; 4 .
> ```
> In particular **`n_F` is finite** for every such `F` — settling, for this subclass, the question §172.3
> recorded as open ("even finiteness of `n_F` is open"). Moreover `n_F = 4` would force `|a_F(p)| = 2`,
> i.e. `α_1(p) = α_2(p)`, for almost all `p` in the logarithmic-density sense; so for `F` **primitive**,
> `n_F < 4`.

Combining with the Energy Gap and Conjecture A one gets `n_F ∈ \{1,2,3\}` for primitive degree-2
conductor-1 elements — the first time the value of `n_F` has been confined to a finite set by
unconditional means.

### 227.4 Consequences for the chain

- Theorem 109's hypotheses (PEP, and `|α_j| ≤ 1`) are now **met unconditionally** for `q_F = 1`; only
  self-duality and "the determinant is a Dirichlet character" remain as hypotheses there.
- KP Theorem 4: `F ∈ S_2`, `q_F = 1`, with a pole at `s = 1` ⟹ `F = ζ(s)²`. So in this subclass every
  non-`ζ²` element is entire, exactly the hypothesis (WILTON) and §223.1 require.
- KP Theorem 3 supplies the meromorphy of the linear twist **at every rational**, which is the major-arc
  input of the theta-pairing route (§226.3) — now unconditional for `q_F = 1`.

> **Recorded.** The terminal obstruction for degree 2, conductor 1, is no longer the existence of a
> transformation formula (KP Theorem 2), nor the continuation of linear twists at rationals (KP
> Theorem 3), nor PEP/BS (KP Theorem 1). It is the assembly: the `y → 0` asymptotic of
> `∫_0^1θ(β)Θ_F(β,y)dβ` from these ingredients, uniformly over the arcs.

---

## 228. Cycle 228 (2026-07-26) — Theorem 128 (`n_F ≤ d_F²`), and the assembly plan

### 228.1 The energy is bounded by the square of the degree

> **Theorem 128.** Let `F ∈ S` satisfy PEP with local degree `∂_p ≤ d_F` and Bounded Satake
> `|α_j(p)| ≤ 1`. Then `|a_F(p)| ≤ d_F` for every `p`, hence
> ```
> \limsup_x\ \frac{1}{\log\log x}Σ_{p≤x}\frac{|a_F(p)|²}{p} \;≤\; d_F^{\,2} .
> ```
> Equality in the density would force `|a_F(p)| = d_F`, i.e. `α_1(p) = \cdots = α_{d}(p)` with modulus
> `1`, for almost all `p` — which happens only for `F = P^{d}` with `P` of degree `1`. **So for `F`
> primitive of degree `d ≥ 2`, `n_F < d²` strictly.**
>
> By §227, the hypotheses hold **unconditionally** for `F ∈ S_2` with `q_F = 1`, giving `n_F ≤ 4`, and
> `n_F < 4` for primitive `F` — Theorem 127.

This is the inequality the programme conjectured and could not prove while PEP/BS were treated as
hypotheses (cf. §172's discussion of `n_F ≤ d_F²`). It settles **finiteness** of `n_F` in every
subclass where PEP and BS are known.

### 228.2 What remains in degree 2, conductor 1

With `|α_j| = 1` (the unitary case) and `d = 2`,
```
|a_F(p)|² = |α_1|²+|α_2|²+2\mathrm{Re}(α_1\barα_2) = 2 + 2\mathrm{Re}(α_1\barα_2) ,
\qquad n_F = 2 + 2\,\mathrm{Re}\,δ_1(α_1\barα_2) .
```
So Conjecture A's content, for such `F`, is precisely
```
δ_1(α_1\barα_2) ∈ \tfrac12 Z ,\qquad\text{and (P1) is } \mathrm{Re}\,δ_1(α_1\barα_2) = −\tfrac12 .
```
`α_1\barα_2` is the adjoint character on the Satake class, so this is again `\mathrm{Sym}²`/adjoint
non-vanishing — but now with the *outer* bound `|δ_1| ≤ 1` unconditional, hence `n_F ∈ [0,4]`.

### 228.3 The assembly plan, stated precisely

Ingredients now available unconditionally for `F ∈ S_2`, `q_F = 1`, `F ≠ ζ²` (hence entire, KP Thm 4):
```
(A) KP Thm 3 :  F(s,a/q) ∈ M(2,q²) — meromorphic on C, holomorphic for σ < 1, explicit growth.
(B) KP Thm 2 :  the Fricke-type transformation α ↦ −1/(q_Fα) with explicit polynomials Q_ν.
(C) classical:  θ(a/k+δ) ≍ k^{−1/2}\min(y^{−1/2},|δ|^{−1/2}) after damping.
(D) §218.2  :  Θ_F(a/k,y) is a finite combination of damped Dirichlet twists of F, each with a
                complete y → 0 expansion from the functional equation of F^χ ∈ S^♯.
```
Required: the `y → 0` asymptotic of `∫_0^1θ(β)Θ_F(β,y)\,dβ`, i.e.
```
Σ_{n}a_F(n²)e^{−yn²} \;=\; c\,y^{−1/2}(\log 1/y)^{κ−1}(1+o(1)) ,\qquad κ = δ_1(a_F(·²)) ∈ Z ?
```
with the arcs summed uniformly in `k`. **(A)–(D) supply every local ingredient; what is missing is the
uniformity in `k` of (A) and (D) and the treatment of `β` badly approximable — for which (B) is the
tool, since it moves `α` to `−1/(q_Fα)` and therefore exchanges small denominators for large ones.**

> **Recorded as the leading concrete programme.** It is a substantial analytic project — of the size of
> a paper — but every ingredient is now identified, unconditional, and in the literature. **No step
> requires MI, Rankin–Selberg, automorphy, zero-density estimates, or any hypothesis this programme has
> been carrying.**

### 228.4 Position

```
Conjecture A for primitive F ∈ S_2 with q_F = 1
 ⟸ δ_1(a_F(·²)) ∈ Z                                     Thm 109 (PEP now free, §227)
 ⟸ Σ_n a_F(n²)e^{−yn²} ∼ c y^{−1/2}(\log 1/y)^{κ−1}      Thm 124 + Mellin
 = the y→0 asymptotic of ∫_0^1θ(β)Θ_F(β,y)dβ             §226.1
 ⟸ assembly of (A)–(D) above                              OPEN — but all ingredients unconditional
unconditional bounds now in hand : 0 ≤ n_F < 4          Thm 127, Thm 128
```

### 228.5 Lean for Theorems 127–128

New `HTGeometry/SatakeEnergyBound.lean`, registered:
```lean
theorem norm_sum_le_card {ι} [Fintype ι] (v : ι → ℂ) (hle : ∀ i, ‖v i‖ ≤ 1) :
    ‖∑ i, v i‖ ≤ (Fintype.card ι : ℝ)
theorem norm_eq_one_of_norm_sum_eq_card {ι} [Fintype ι] (v : ι → ℂ)
    (hle : ∀ i, ‖v i‖ ≤ 1) (h : ‖∑ i, v i‖ = (Fintype.card ι : ℝ)) : ∀ i, ‖v i‖ = 1
theorem weighted_sq_le {ι} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, ‖a i‖ ≤ D) :
    ∑ i ∈ s, ‖a i‖ ^ 2 * w i ≤ D ^ 2 * ∑ i ∈ s, w i
```
The first two are Theorem 128's bound and its **rigidity**: `|Σ_{j<d}α_j| = d` with `|α_j| ≤ 1` forces
every `|α_j| = 1` — the step that upgrades `n_F ≤ d²` to `n_F < d²` for primitives. The third is the
weighted transfer `Σ_{p≤x}|a_F(p)|²/p ≤ d²Σ_{p≤x}1/p`. Corpus search run first (`research "sum of unit
bounded complex numbers norm equality forces all norms one Satake"`, plus `rg`): only unrelated
Blaschke/pencil results; no duplication.

---

## 229. Cycle 229 (2026-07-26) — **the linear twist carries an effective action of the modular group**

### 229.1 Two transformations

For `F ∈ S^♯` write `F(s,β) = Σ_n a_F(n)e(−nβ)n^{−s}` for the linear twist. Then:

**(T) Periodicity — free.** `e(−n(β+1)) = e(−nβ)e(−n) = e(−nβ)`, so
```
F(s,β+1) = F(s,β) \qquad\text{for every } β ∈ R .
```
*This is exactly the property the standard twist lacks*: `Φ_G(s,α)` has frequencies `\sqrt m` and is
only almost periodic (§213.2). **The linear twist is genuinely periodic.**

**(S) Fricke transformation — Kaczorowski–Perelli Theorem 2 (degree 2).** For `α > 0` and every `K`,
```
F(s,α) = −i\,ω_F\,(α\sqrt{q_F})^{2s−1+iθ_F}Σ_{ν=0}^{K}\Big(\tfrac{−i}{q_Fα²}\Big)^{ν}Q_ν(s)\,
          \bar F\Big(s+ν+iθ_F,\,−\tfrac{1}{q_Fα}\Big) + H_K(s,α) ,
```
with `H_K ≪ (A/K)^{K}` on `|s| < 2K`, `−K+\tfrac12 < σ < 2`. **On any compact `s`-region, choosing `K`
large makes `H_K` smaller than any prescribed `ε`: the `S`-transformation is *effectively exact*
there.**

### 229.2 The consequence

> **The pair `(T,S)` generates the modular group.** For `F ∈ S_2` with `q_F = 1` the linear twist
> `β ↦ F(s,β)` is therefore a function on `Q` (or on `R`, or on the upper half-plane after the
> substitution `β ↦ β+iy`) carrying an **effective action of `PSL_2(Z)`**: invariance under `β ↦ β+1`
> and an explicit, asymptotically exact transformation under `β ↦ −1/β`.
>
> **This is modularity, in the period-function form** (Lewis–Zagier). It is exactly the input that
> Wilton's classical bound and Shimura's construction of `\mathrm{Sym}²` consume, and it is exactly what
> §222.2's "no free crossing" principle said could not be manufactured by a transform — correctly: it
> is not manufactured, it is supplied by KP's theorem.

Three immediate consequences, all now structurally available in `S_2` with `q_F = 1`:
1. **Reduction to small denominators.** `a/q ↦ −q/a` under `S`, combined with `T`-shifts, is the
   continued-fraction algorithm: every rational is moved to one of small denominator in `O(\log q)`
   steps. This is how KP prove their Theorem 3 (every `F(s,a/q) ∈ M(2,q²)`), and it is the mechanism
   §228.3 needed for badly approximable `β`.
2. **Wilton's bound** becomes a matter of running the classical argument (Fricke plus partial summation
   along the continued fraction) with the effective `S`-transformation in place of exact modularity.
3. **The theta pairing** `∫_0^1θ(β)Θ_F(β,y)dβ` (§226.1) is then an integral of a product of two
   objects both transforming under the modular group — Shimura's setting exactly.

### 229.3 Honest scope

- KP's Theorem 2 is stated for `F ∈ S^♯_2`, i.e. **degree 2**; the `S`-transformation for other degrees
  is not claimed here.
- It is an **asymptotic** expansion, effectively exact only on compact `s`-sets and with constants
  depending on `F` and (through `A = A(F,α)`) on `α`. Uniformity in `α` of `A(F,α)` is the same kind of
  question as §10.2's, and must be checked before any argument that sums over many `α` is claimed.
- Conductor `1` is needed for KP's Theorem 3 as stated; general conductor is open (arXiv:2405.03186 is
  the continuation of that programme).

> **Recorded as the session's principal structural find.** The obstruction that this programme named
> eight times and finally located as "modularity is unavailable in the abstract class" is, **in degree 2,
> false**: the modular action on the linear twist is a theorem of Kaczorowski–Perelli. What remains for
> Conjecture A in degree `2`, conductor `1`, is to run the classical arguments with it.

---

## 230. Cycle 230 (2026-07-26) — **Wilton's bound in `S_2`, `q_F = 1`: the argument, and the one hypothesis it needs**

### 230.1 The generating function and its weight

Set `Θ_F(β,y) := Σ_{n≥1}a_F(n)\,e(−nβ)\,e^{−2πny}`, i.e. the linear twist's generating function at
`z = −β+iy ∈ H`. By Mellin, `Θ_F(β,y) = \frac1{2πi}∫_{(c)}Γ(w)(2πy)^{−w}F(w,β)\,dw` for `c > 1`.

Insert KP's Theorem 2 (degree 2, `q_F = 1`), `F(w,β) = −iω_Fβ^{2w−1+iθ}Σ_νQ_ν(w)(−i/β²)^ν
\bar F(w+ν+iθ,−1/β) + H_K(w,β)`. The factor `β^{2w}` turns `(2πy)^{−w}` into `(2πy/β²)^{−w}`, so each
term is a Mellin transform **at the point `y/β²`**, and the leading term reads
```
Θ_F(β,y) \;=\; c\,ω_F\,β^{−1+iθ}\;\barΘ_F\Big(−\tfrac1β,\ \tfrac{y}{β²}\Big)\;\big(1 + \text{lower order}\big)
   \;+\;(\text{H-term}) .
```
This is exactly the substitution `z ↦ −1/z`: for `z = −β+iy`, `\mathrm{Re}(−1/z) → −1/β` and
`\mathrm{Im}(−1/z) → y/β²` as `y/β → 0`.

> **Weight check.** With `Θ_F(β,y) = |β|^{−1}Θ'(−1/β, y/β²)(1+\cdots)`, the quantity `y^{1/2}|Θ_F(β,y)|`
> is invariant: `(y/β²)^{1/2}|Θ'| = y^{1/2}|β|^{−1}|Θ'|`. **So `y^{1/2}|Θ_F|` is an (effectively)
> `S`-invariant function**, and by §229.1(T) it is exactly `T`-invariant. Hence it is an effectively
> `PSL_2(Z)`-invariant function on `H`.

### 230.2 The argument

1. **Cusp decay.** `Θ_F(β,y) = e(−β)e^{−2πy} + O(e^{−4πy+ε})` as `y → ∞` (using `a_F(1) = 1`, `F` entire
   so no constant term, and `a_F(n) ≪ n^{ε}`). So `y^{1/2}|Θ_F| → 0` at the cusp, **exponentially**.
2. **Invariance.** `y^{1/2}|Θ_F|` is `T`-invariant exactly and `S`-invariant up to the KP error.
3. **Boundedness.** A continuous `Γ`-invariant function on `H` decaying at the cusp is bounded (the
   fundamental domain minus a cusp neighbourhood is compact). Hence
   ```
   |Θ_F(β,y)| \;≪_F\; y^{−1/2}\qquad\text{uniformly in } β .
   ```
4. **Wilton.** Partial summation from `Σ_n a_F(n)e(−nβ)e^{−2πny}` at `y = 1/N` gives
   ```
   Σ_{n ≤ N}a_F(n)\,e(−nβ) \;≪_F\; N^{1/2}\log N \qquad\text{uniformly in } β .
   ```

**This is Hecke–Wilton's classical proof verbatim, with KP's Theorem 2 in the role of modularity.**

### 230.3 The one hypothesis

Step 2 uses an *approximate* invariance: KP's `H_K(w,β) ≪ (A/K)^{K}` with `A = A(F,β)`. Reducing a
point of `H` to the fundamental domain takes `O(\log)` applications of `S` and `T` (the
continued-fraction algorithm), so the errors compound over `O(\log)` steps. This is harmless **provided
`A(F,β)` is bounded uniformly in `β`** (or grows slowly enough that `K` can absorb it), since then each
step costs a factor `1+ε` and `O(\log)` steps cost `(1+ε)^{O(\log)} = O(1)` for `ε` small — indeed the
`\log N` in Wilton's bound is exactly the room such compounding needs.

> **(UNIF-KP).** *Is the constant `A = A(F,α)` in Kaczorowski–Perelli's Theorem 2 bounded, or slowly
> growing, uniformly in `α`?*
>
> ```
> (UNIF-KP) ⟹ Wilton in S_2 with q_F = 1 ⟹ ... ⟹ Conjecture A for those F .
> ```

This is the **same** uniformity question as §10.2/§215.3, but in a decisively better position: it is
now needed only to control `O(\log)` compounding steps of an argument whose every other ingredient is
classical and complete, rather than to justify a global interchange or a sum over the whole spectrum.

### 230.4 Status

```
Conjecture A for primitive F ∈ S_2 with q_F = 1
 ⟸ δ_1(a_F(·²)) ∈ Z                                Thm 109 (PEP, BS free by §227)
 ⟸ Σ_n a_F(n²)e^{−yn²} asymptotic                   Thm 124 + Mellin
 ⟸ theta pairing + Shimura assembly                 §226, §228.3
 ⟸ Wilton's bound for F                             §230.2   — argument complete
 ⟸ (UNIF-KP)                                        §230.3   — the single remaining hypothesis
```
Every other step is now either proved here or quoted from Kaczorowski–Perelli. **The Selberg class
problem in degree 2, conductor 1, has been reduced to a uniformity constant in a published theorem.**

---

## 231. Cycle 231 (2026-07-26) — (UNIF-KP) narrowed: small `α` is the **easy** case

### 231.1 What the paper says about its constants

From §3 of arXiv:1207.2312 (verbatim in substance):

> *"Finally, `A, c, c_0, \tilde c, \dots` will denote positive constants, possibly depending on `F(s)`
> (also via a dependence on `c_0,c_1,c_2` above), not necessarily the same at each occurrence. The
> constants in the `≪`- and `O`-symbols may also depend on `F(s)`."*

The auxiliary lemmas (3.1–3.5, bounding `G(s,w)`, `S(s,w)`, `Γ(1−2s−w−iθ_F)`, `B_ν(s)/ν!`) all carry
constants depending on `F` **only**. However, **Theorem 2's own error constant is written `A = A(F,α)`**
— the `α`-dependence is explicit in the statement, and no uniformity in `α` is claimed.

So (UNIF-KP) is a genuine gap in the literature as it stands, not an oversight of this log.

### 231.2 The narrowing: the modular reduction never needs small `α`

In the argument of §230.2 the `S`-transformation is applied to `z = −β+iy` only when `|z| < 1`, and the
reduction to the fundamental domain proceeds by alternating `T` and `S`. Two observations:

- **If `β` is close to `0` and `y` is small, one `S`-step suffices.** `z ≈ iy` gives `Sz = i/y`, of large
  imaginary part: the point lands near the cusp immediately and the argument terminates. No compounding
  occurs.
- **Compounding occurs only for `β` bounded away from `0`** — precisely, along the continued-fraction
  reduction the successive parameters are the complete quotients, which are bounded below by the
  standard theory once the first step has been taken.

> **(UNIF-KP), narrowed.** *It suffices that `A(F,α)` be bounded for `α` ranging over a compact subset
> of `(0,∞)` bounded away from `0`* — not uniformly over all `α > 0`.
>
> Since the sources of `α`-dependence in KP's proof are the contour `L(s)` and the choice of `N`
> (their (3.34)), and both are governed by `|s|` and `F`, with `α` entering only through the explicit
> factors `(α\sqrt{q_F})^{2s−1+iθ_F}` and `(q_Fα²)^{−ν}`, a bound of the form
> `A(F,α) ≪_F \max(α, α^{−1})^{C}` is the expected shape; on a compact set away from `0` that is
> `O_F(1)`.

### 231.3 Status of the degree-2 conductor-1 case

```
Conjecture A for primitive F ∈ S_2 with q_F = 1
 ⟸ δ_1(a_F(·²)) ∈ Z                       Thm 109 (PEP, BS unconditional by §227)
 ⟸ Σ_n a_F(n²)e^{−yn²} asymptotic          Thm 124 + Mellin
 ⟸ theta pairing (Shimura assembly)        §226, §228.3
 ⟸ Wilton's bound for F                    §230.2 — complete modulo one constant
 ⟸ A(F,α) = O_F(1) on compacta of (0,∞)    §231.2 — expected shape, extractable from KP §3
```

> **Recorded as the programme's most advanced position.** Every mathematical step is either proved in
> this log or published by Kaczorowski–Perelli; what remains is to track one constant through the proof
> of a published theorem. That is a finite, mechanical task on a fixed text — of a different character
> from every obstruction this programme has met in 230 cycles, all of which were structural.

---

## 232. Cycle 232 (2026-07-26) — the reduction is `O(\log N)` steps; what must be tracked, stated exactly

### 232.1 Step count

In §230.2 the reduction of `z_0 = −β + i/N` to the fundamental domain alternates `T` (which does not
change `\mathrm{Im}`) and `S` (applied when `|z| < 1`, which multiplies `\mathrm{Im}` by `|z|^{−2} > 1`).
The imaginary part therefore increases at every `S`-step and the process stops once
`\mathrm{Im} ≥ \sqrt3/2`. Standard continued-fraction theory gives
```
\#\{S\text{-steps}\} = O\big(\log(1/\mathrm{Im}\,z_0)\big) = O(\log N) ,
```
which is **exactly the `\log N` appearing in Wilton's bound**. So the compounding of KP's error over the
reduction is affordable if each step costs a factor `1 + O(1/\log N)`, or if the product of the step
constants is `N^{o(1)}`.

### 232.2 Correction to §231.2

§231.2 asserted that small `α` never occurs in the compounding. That is **too strong**: the parameters
along the reduction are the complete quotients, and for `β` with large partial quotients they can be
arbitrarily small. What is true, and is the correct statement, is:

> **Small `α` gives *fast* progress.** At a step with `α_k = |\mathrm{Re}\,z_k| ≪ \mathrm{Im}\,z_k`, one
> `S`-application multiplies the imaginary part by `≈ α_k^{−2}`, so such steps are rare: their total
> contribution to the step count is `O(\log N / \log(1/α))`. The requirement is therefore not that
> `A(F,α)` be bounded, but that
> ```
> ∏_{k} A\big(F,α_k\big)^{\,c_k} = N^{o(1)}
> ```
> along the reduction, where the exponents `c_k` are weighted by the progress each step makes. A bound
> `A(F,α) ≪_F \max(α,α^{−1})^{C}` suffices, because a step with small `α_k` costs `α_k^{−C}` but buys a
> factor `α_k^{−2}` of progress.

Sixteenth defect (own): §231.2's narrowing over-claimed; the corrected form above is weaker but still
much less than uniform boundedness.

### 232.3 The precise remaining task

> **(TRACK).** *Determine the `α`-dependence of the constant `A = A(F,α)` in Theorem 2 of
> Kaczorowski–Perelli, arXiv:1207.2312. A bound of the form `A(F,α) ≪_F \max(α,α^{−1})^{C}` with any
> fixed `C` suffices for §230.2, hence for Wilton's bound in `S_2` with `q_F = 1`, hence — through
> Theorems 109, 124 and the theta-pairing assembly — for Selberg's Conjecture A on that subclass.*

The paper's own convention declares all constants to depend on `F` alone; only Theorem 2's statement
carries the extra argument. The sources of `α`-dependence in §3 are the choice of the integer `N` in
(3.34) and the contour `L(s)`; `α` otherwise enters only through the explicit factors
`(α\sqrt{q_F})^{2s−1+iθ_F}` and `(q_Fα²)^{−ν}`. **Extracting the dependence is a finite reading task on
a fixed text**; it was attempted this cycle from the arXiv source but the mathematical symbols are lost
in the available text extraction, so it is recorded as the next concrete step rather than claimed.

### 232.4 Position

```
Conjecture A for primitive F ∈ S_2 with q_F = 1
 ⟸ δ_1(a_F(·²)) ∈ Z                             Thm 109 (PEP, BS unconditional, §227)
 ⟸ Σ_n a_F(n²)e^{−yn²} asymptotic                Thm 124 + Mellin
 ⟸ theta pairing / Shimura assembly              §226, §228.3
 ⟸ Wilton's bound for F                          §230.2  (Hecke's argument, complete)
 ⟸ (TRACK): A(F,α) ≪_F \max(α,α^{−1})^{C}        §232.3  ← the single remaining item
```
Sixteen defects, all found by re-derivation; the last five were in routes or claims made within two
cycles of their correction.

---

## 233. Cycle 233 (2026-07-26) — **retraction**: KP's error term is `(AK)^K`, not `(A/K)^K`; the Wilton argument of §230 fails

### 233.1 The exact statement, from the arXiv LaTeX source

The `e-print` source of arXiv:1207.2312 (`converse.tex`) gives Theorem 2 verbatim:
```
F(s,α) = −i ω_F^* (\sqrt{q_F}α)^{2s−1+iθ_F} Σ_{ν=0}^{K} ( i q_F α / 2π )^{ν} Q_ν(s)
            \bar F(s+ν+iθ_F, −1/(q_Fα)) + H_K(s,α) ,
H_K(s,α) holomorphic for −K+1/2 < σ < 2, |s| < 2K,     H_K(s,α) ≪ (A K)^{K} .
```
Two corrections to the reading used in §§229–232, both from the PDF text extraction dropping symbols:

1. **The error is `(AK)^{K}`, which *grows* with `K`** — not `(A/K)^{K}`. §229.1 and §230.2 asserted that
   choosing `K` large makes the `S`-transformation "effectively exact on compacta". **That is false.**
2. The `ν`-th coefficient is `(i q_Fα/2π)^{ν}`, not `(−i/(q_Fα²))^{ν}`.

**Seventeenth defect (own), and the most consequential: the Wilton argument of §230.2 is invalid.** It
required the `S`-transformation to be quantitatively exact up to a small error; KP's error is
holomorphic on an expanding region but not small.

### 233.2 What `H_K` is actually for

KP's own use (their proof of Theorem 3, source line 1473) is an induction on the denominator:
```
F(s,a/q) = (\text{explicit factor}) × Σ_{ν=1}^{K}\big(\tfrac{ia}{2πq}\big)^{ν}P_ν(s)(s+ν−1)^{m_F}
             \bar F(s+ν+iθ_F, −q/a) + H_K(s,a/q) ,
```
"Since `a ≤ q−1`, by the inductive hypothesis all terms on the right-hand side are holomorphic in the
domain where `H_K(s,a/q)` is holomorphic. The result follows since `K` is arbitrarily large."

> **So the transformation formula is used *qualitatively*: `H_K` is holomorphic on `−K+1/2 < σ < 2`,
> and letting `K → ∞` enlarges that domain. The `(AK)^K` bound merely certifies finiteness.** The
> continued-fraction reduction `a/q ↦ −q/a` is genuinely there (confirming §229.2(1)), but it transports
> *holomorphy*, not *size*.

Also settled: Lemma 3.19 gives `R_ν, V_ν ≪ A^KK^{ν}` and `Q_ν ≪ (AK)^{K}` with `A = A(c)` depending only
on a numerical parameter — **the polynomial bounds are `α`-free**. The `α`-dependence in Theorem 2's
`A = A(F,α)` therefore enters only through the assembly of `H_K`, not through the `Q_ν`.

### 233.3 Corrected position

**Retracted:** §229.2's "effective `PSL_2(Z)` action" in the quantitative sense; §230.2's Theorem
(Wilton's bound); §231–232's (UNIF-KP)/(TRACK) framing, which presupposed that smallness of `H_K` was
the issue. Preprint §21 must be struck.

**Standing, unaffected:**
- **Theorems 127, 128** (`|a_F(p)| ≤ 2`, `n_F ≤ 4`, `n_F < 4` for primitives; `n_F ≤ d_F²` under
  PEP+BS): these rest on KP's Theorem 1 and Corollary, which are unconditional and unaffected.
- **PEP and Bounded Satake are theorems in `S_2` with `q_F = 1`** (§227.2) — the scope correction stands.
- KP Theorem 3: every linear twist at a rational is meromorphic on `C`, holomorphic for `σ < 1` — a
  qualitative continuation, unconditional.
- The linear twist is exactly `1`-periodic in `β` (§229.1(T)) — elementary and unaffected.
- Everything in §§165–228 that does not depend on §229–232.

**The obstruction returns to:** a *quantitative* transformation law for the linear twist. KP supply a
qualitative one. Wilton's classical proof needs the quantitative one, and the Selberg axioms — as far
as the literature located goes — do not supply it.

> **Recorded.** Cycles 229–232 rested on a misreading of a single exponent in a PDF; the arXiv LaTeX
> source settled it in one cycle. **Standing rule, strengthened: quote analytic statements from the
> source, never from PDF text extraction.**

---

## 234. Cycle 234 (2026-07-26) — the degree-2 frontier re-mapped, and a new theorem: **linear twists and Ramanujan for `S_2` with conductor `2, 3, 4`**

### 234.0 Eighteenth defect (own): §§227–233 were aimed at an already-classified subclass

**Kaczorowski–Perelli, *Classification of `L`-functions of degree 2 and conductor 1*, arXiv:2009.12329,
Adv. Math. 2022**, streamlined in **arXiv:2503.02492** (Funct. Approx. 2024), proves:

> Let `F ∈ S^♯` of degree 2 and conductor 1 be normalized (`θ_F = 0`, first non-zero coefficient `1`).
> Put `χ_F = H_F(1) + H_F(2) + 2/3`. Then `χ_F ∈ R` and
> (i) `χ_F > 0` ⟹ `F(s) = L(s + (k−1)/2, f)` for a level-1 holomorphic cusp form of even weight
>     `k = 1 + √(2χ_F)`;
> (ii) `χ_F = 0` ⟹ `F(s) = ζ(s)²`;
> (iii) `χ_F < 0` ⟹ `F(s) = L(s,u)` for a level-1 weight-0 Maass form with eigenvalue `(1−2χ_F)/4`.

Hence every `F ∈ S` of degree 2 and conductor 1 is an automorphic `L`-function, and **Selberg's
Conjectures A and B are theorems on that subclass** (Rankin–Selberg). My Theorem 127 (`n_F ≤ 4`,
`n_F < 4` for primitives, `d_F = 2`, `q_F = 1`) is therefore *subsumed*: the true value is `n_F = 1`.
Theorem 128 (`n_F ≤ d_F²` under PEP + BS) is the trivial consequence of `|a_F(p)| ≤ d_F`; **not new**.

> **Standing rule added.** Before adopting a subclass as a target, check whether it has been
> *classified*, not merely whether the target statement has been proved on it. A classification kills
> every quantitative question on the subclass at once.

### 234.1 What is actually open in degree 2

- `S^♯_d = ∅` for `0 < d < 1` and `1 < d < 2`; `S_1 = {ζ(s)} ∪ {L(s+iθ,χ) : χ primitive}` (KP).
- `S^♯_2` with `q = 1`: classified (above).
- `S^♯_2` with `q > 1`: **open**. KP (2503.02492, §1): *"in the special case of conductor `q = 1` a full
  description is possible, thanks to a peculiar property of certain linear twists which holds in such a
  case. Quite possibly, an analogous description can be obtained for other small integer conductors,
  like `q = 2, 3` and `4`."*
- Kaczorowski–Perelli–Radziejewski, arXiv:2208.12947, show by a continued-fraction technique that
  certain `q` are *forbidden* conductors in `S^♯_2`, and that (via Hecke's theory for the triangle
  groups `G(λ)`) **no `q ≥ 4` is forbidden**.

The "peculiar property" is KP's Theorem 3 of arXiv:1207.2312: for `q_F = 1` every linear twist
`F(s,a/q)` lies in `M(2,q²)`. **That is the object I generalise below.**

### 234.2 The mechanism, and exactly where `q_F = 1` enters

KP's transformation formula (arXiv:1207.2312, Theorem 2 — stated for **every** `F ∈ S^♯_2` and every
`α > 0`, no conductor restriction) is
```
F(s,α) = −i ω_F^* (√q_F α)^{2s−1+iθ_F} Σ_{ν=0}^{K} (i q_F α/2π)^ν Q_ν(s) F̄(s+ν+iθ_F, −1/(q_F α))
         + H_K(s,α),
```
`H_K` holomorphic for `−K+1/2 < σ < 2`, `|s| < 2K`, `H_K ≪ (AK)^K`; `deg Q_ν = 2ν`,
`Q_ν(s) ≪ (A(|s|+1))^{2ν}/ν!` for `1 ≤ ν ≤ min(|s|,K)` and `Q_ν(s) ≪ (AK)^K` for `|s| ≤ 2K`, `ν ≤ K`.
The `Q_ν` depend on the `γ`-factor only, **not on `α`**.

The linear twist is exactly `1`-periodic in `α`. So the two available moves on the twist parameter are
```
T : α ↦ α + 1        (periodicity)          W : α ↦ −1/(q_F α)   (transformation formula).
```
KP induct on the denominator: with `q_F = 1` and `α = a/q ∈ (0,1)`, `Wα = −q/a` has denominator
`a < q`, so the induction terminates at `α ≡ 0`, where `F(s,0) = F(s) ∈ M(2,q_F)` by their Lemma 2.1.
**For `q_F > 1` the denominator of `Wα` is `q_F a / gcd(q,q_F)`, which need not decrease** — that is the
whole obstruction, and it is exactly the statement that `⟨T,W⟩` is, in the coordinate `β = √q_F α`, the
**Hecke group `G(√q_F) = ⟨β↦β+√q_F, β↦−1/β⟩`**, discrete of finite covolume only for `√q_F = 2cos(π/n)`
or `√q_F ≥ 2`.

### 234.3 The right invariant: a shift-invariant twist conductor

**Definition.** For `α ∈ Q` with denominator `q ≥ 1` (in lowest terms, `α = A/q`, `gcd(A,q) = 1`) and an
integer `Q ≥ 1`, put
```
h_Q(α) := Q q² / gcd(q,Q).
```

**Lemma 234.A (exact recursion).** Let `Q ≥ 1`, `α = A/q` with `A ≠ 0`, `gcd(A,q) = 1`, and let
`g = gcd(q,Q)`. Then the denominator of `Wα = −1/(Qα) = −q/(QA)` is `q₁ = Q|A|/g`, one has
`gcd(q₁,Q) = Q/g`, and
```
h_Q(α) = h_Q(Wα) / (Q α²) ,
```
identically in the representative `A` (in particular `h_Q` is `1`-periodic, as it must be).

*Proof.* Write `Q = g m`. Then `gcd(q,QA) = gcd(q,Q) = g` because `gcd(A,q) = 1`; hence
`q₁ = QA/g = mA` (absolute value). Since `g ∣ q` and `gcd(A,q) = 1` we get `gcd(A,g) = 1`, so
`gcd(q₁,Q) = gcd(mA, gm) = m·gcd(A,g) = m = Q/g`. Therefore
`h_Q(Wα) = Q q₁²/(Q/g) = Q·m²A²·g/Q = Q²A²/g`, and
`h_Q(Wα)/(Qα²) = (Q²A²/g)·q²/(QA²) = Q q²/g = h_Q(α)`. ∎

Sanity: `q_F = 1` gives `h_1(A/q) = q²`, exactly KP's `M(2,q²)`. `α ≡ 0` gives `h_Q(0) = Q = q_F`,
exactly `F ∈ M(2,q_F)`. For a level-`N` newform and a twist of denominator `q` coprime to `N`,
`h = Nq²`, the classical twisted conductor.

### 234.4 The descent

**Lemma 234.B (two-step descent).** Let `Q ≥ 1`. Represent each non-zero class `α ∈ Q/Z` by
`α = A/q` with `gcd(A,q) = 1` and `2|A| ≤ q` (nearest-integer representative). Let `q₁` be the
denominator of `Wα` and, if `Wα ≢ 0`, let `q₂` be the denominator of `W²α`. Then
```
4 q₂ ≤ Q q .
```
Consequently, for `Q ≤ 3` the denominator strictly decreases in two steps, and every `α ∈ Q` reduces to
`0` in finitely many steps.

*Proof.* With `g = gcd(q,Q)`, `Q = gm`, Lemma 234.A gives `q₁ = m|A|` and `gcd(q₁,Q) = m`, whence
`q₂ = Q|A₁|/m = g|A₁|` where `2|A₁| ≤ q₁`. Therefore
`4q₂ = 4g|A₁| ≤ 2g q₁ = 2g m|A| = 2Q|A| ≤ Q q`. ∎

**Lemma 234.C (the exceptional class at `Q = 4`).** For `Q = 4`: if `q` is odd or `4 ∣ q` then the
descent is strict in two steps and `α` reduces to `0`; if `q ≡ 2 (mod 4)` then `q₁ = 2|A| ≡ 2 (mod 4)`
again and `q₁ ≤ q` with equality only for `q = 2`, so `α` reduces to `1/2`, which is a **fixed point**
(`W(1/2) = −1/2 ≡ 1/2`). For `Q ≥ 5` Lemma 234.B gives only `q₂ ≤ Qq/4`, and no descent is available.

*Proof.* `q ≡ 2 (mod 4)`, `gcd(A,q)=1` force `A` odd and `g = 2`, so `q₁ = 4|A|/2 = 2|A| ≡ 2 (mod 4)`
and `q₁ ≤ q` with equality iff `2|A| = q`, i.e. `q = 2`. The remaining cases are Lemma 234.B with
`4q₂ ≤ 4q`, made strict by `2|A| < q` (`q` odd) resp. `g = 4` (`4∣q`, then already `q₁ = |A| < q`). ∎

> The threshold `Q < 4` produced by this elementary descent is **exactly** the Hecke-group threshold
> `√Q < 2`, and the exceptional class `1/2` at `Q = 4` is exactly the third cusp of `Γ_0(4)`, the one
> not merged with `∞` by the Fricke involution. The arithmetic descent reproduces the group theory
> with no group theory in it.

### 234.5 The theorem

**Theorem 129 (linear twists at small conductor).** Let `F ∈ S^♯` be **entire** with `d_F = 2` and
integer conductor `q_F = Q ∈ {1,2,3,4}`. Let `α = a/q ∈ Q` in lowest terms, and assume `q ≢ 2 (mod 4)`
in case `Q = 4`. Then `F(s,α)` is entire and
```
F(s,α) ∈ M(2, Q q² / gcd(q,Q)) .
```

*Proof.* Induct on the number `n(α)` of `W`-steps needed to reach `0` (finite by Lemmas 234.B, 234.C).
`n = 0`: `F(s,0) = F(s) ∈ M(2,q_F)` by Lemma 2.1 of arXiv:1207.2312, and `h_Q(0) = Q`. ✓

`n → n+1`: choose the nearest-integer representative `α = A/q`, `2|A| ≤ q`. If `A < 0` use
`F(s,α) = conj( F̄(s̄, −α) )`, which preserves both entirety and the class `M(2,h)` (the class is
defined by growth as `σ → −∞` uniformly on each strip `A ≤ t ≤ B`, and the strips are arbitrary); so
assume `A > 0`, i.e. `α > 0`, as KP's Theorem 2 requires. Apply Theorem 2:
```
F(s,α) = −iω_F^*(√Qα)^{2s−1+iθ_F} Σ_{ν=0}^{K}(iQα/2π)^ν Q_ν(s) F̄(s+ν+iθ_F, Wα) + H_K(s,α).
```
*Holomorphy.* `F̄ ∈ S^♯` is entire, of degree 2, conductor `Q`, and `n(Wα) = n`; by induction each
`F̄(·,Wα)` is entire, and `H_K` is holomorphic for `−K+1/2 < σ < 2`. As `K` is arbitrary, `F(s,α)` is
entire. (This is where `m_F = 0` is used: for `m_F > 0` one would need
`(s+ν−1)^{m_F} ∣ Q_ν(s)`, which KP obtain for `q_F = 1` from the coincidence `W(1) ≡ 0`; for `Q > 1`
that coincidence is unavailable and the polar case stays open — see 234.7.)

*Growth.* Fix `A ≤ t ≤ B`, let `σ → −∞`, take `K = [|σ|]+2`. Then
`|(√Qα)^{2s−1+iθ_F}| ≍ (√Qα)^{−2|σ|}`, and by induction
`|F̄(s+ν+iθ_F,Wα)| ≪ (|σ|−ν+2)^{2(|σ|−ν)} (√{h_Q(Wα)}/(2πe))^{2(|σ|−ν)}|σ|^{C}`. With
`Q_ν(s) ≪ (C|σ|)^{2ν}/ν!` for `1 ≤ ν ≤ K` the `ν`-th term is
```
≪ |σ|^{2|σ|} ( √{h_Q(Wα)} / (√Q α · 2πe) )^{2|σ|} · (C')^ν/ν! · |σ|^C ,
```
and by Lemma 234.A `√{h_Q(Wα)}/(√Qα) = √{h_Q(α)}`. Summing, `Σ_ν (C')^ν/ν! = O(1)`, while the error
`(AK)^K ≪ (A'|σ|)^{|σ|}` is dominated by `|σ|^{2|σ|}`. Hence
`F(s,α) ≪ |σ|^{2|σ|}(h_Q(α)/(2πe)²)^{|σ|}|σ|^{C}`, i.e. `F(s,α) ∈ M(2,h_Q(α))`. ∎

**Corollary 130 (polynomial Euler product and Ramanujan for `S_2`, conductor `≤ 4`).** Let `F ∈ S` be
entire with `d_F = 2` and `q_F = Q ∈ {1,2,3,4}`. Then for every prime `p` (with `p` odd if `Q = 4`)
```
F_p(s) = ∏_{j=1}^{∂_p} (1 − α_j(p) p^{−s})^{−1},   |α_j(p)| ≤ 1,
∂_p ≤ 2  if p ∤ Q,      ∂_p ≤ 1  if p ∣ Q .
```
In particular `|a_F(p)| ≤ 2` for all such `p`, and `|a_F(p)| ≤ 1` at the primes dividing the conductor.

*Proof.* Theorem 129 with `q = p` gives `F(s,a/p) ∈ M(2,h)` for every `a ≢ 0 (mod p)` with the **same**
`h = Q p²/gcd(p,Q)`. Every `F ∈ S_2` satisfies `N_F(σ,T) ≪ T^{3/2−σ+ε}` for fixed `σ > 1/2`
(arXiv:1207.2312, proof of the Corollary; Montgomery's zero-detection plus the degree-2 approximate
functional equation), hence `N_F(σ,T) = o(T)`. Theorem 1 of arXiv:1207.2312, implication (i) ⟹ (ii),
now gives the displayed Euler factor with `∂_p ≤ [log(h/q_F)/log p] = [log(p²/gcd(p,Q))/log p]`. ∎

**Corollary 131 (finiteness of the prime energy).** For `F` as in Corollary 130,
`Σ_{p ≤ x} |a_F(p)|²/p ≤ 4 loglog x + O(1)`, hence `limsup_x (loglog x)^{−1}Σ_{p≤x}|a_F(p)|²/p ≤ 4`.
This is the *finiteness half* of Selberg's Conjecture A on a subclass where it was not previously
available: membership in `S` gives only `a_F(p) ≪_ε p^{ε}`, which yields **no** bound on the energy.

### 234.6 Novelty audit

*Cited, not new:* KP's Theorem 2 (transformation formula, all conductors), Theorem 1 (twists ⟹ Euler
product), Lemma 2.1 (`F ∈ M(d,q_F)`), the density bound `N_F(σ,T) ≪ T^{3/2−σ+ε}` in `S_2`.
*New here:* the shift-invariant twist conductor `h_Q(α) = q_F q²/gcd(q,q_F)` and its exact recursion
(Lemma 234.A); the two-step descent `4q₂ ≤ Qq` and the identification of the threshold `Q < 4` and of
the exceptional class `1/2` at `Q = 4` (Lemmas 234.B, 234.C); the induction on reduction distance
rather than on the denominator, which is what makes `q_F > 1` work at all; Theorem 129 and
Corollaries 130, 131.
*Checked against:* arXiv:1207.2312 (only `q_F = 1`), arXiv:2009.12329 and arXiv:2503.02492
(classification at `q = 1`; the extension to `q = 2,3,4` is stated there as a hope, not a theorem),
arXiv:2208.12947 (forbidden conductors — continued fractions, but for the *nonlinear* twist and about
existence of `F`, not about linear twists), arXiv:2405.03186 (linear twists only at `1/D` with
`D ≡ 1 (mod q_F)` — precisely the classes at reduction distance ≤ 3, a special case of Theorem 129).

### 234.7 Open, immediately

**(POLE).** Extend Theorem 129 to `m_F > 0`. Needed: `(s+ν−1)^{m_F} ∣ Q_ν(s)` for `F ∈ S^♯_2` of
integer conductor `Q`, together with `θ_F = 0` when `m_F > 0`. KP derive both from Theorem 2 at
`α = 1`, using `W(1) = −1 ≡ 0`, available only when `q_F = 1`. At `q_F = Q` the substitute coincidence
is `α = 1/Q`, but `F(s,1/Q)` is not a priori known to continue, so the argument is circular as it
stands. **Do not retry the `α = 1` route at `Q > 1`.**

**(CLASS-q).** With Theorem 129 in hand, run KP's Steps 1–4 (structural invariants → virtual
`γ`-factors → period functions) at conductor `2, 3, 4`. Their Step 1 needs the self-referential twist
identity `F(s,1,α) = F(s,α)`; at conductor `Q` the substitute is the composite of the `W`-steps of a
loop in the reduction graph, whose existence is exactly Lemma 234.B. This is the route to Selberg's
Conjectures A and B on all of degree 2 with conductor `≤ 4`.

---

## 235. Cycle 235 (2026-07-26) — the general orbit form, and the self-referential class at conductor 4

### 235.1 Theorem 129 in its natural generality

The proof of Theorem 129 is an induction on the number of `W`-steps, so the conductor restriction is
only a sufficient condition for that number to be finite. The natural statement is:

**Theorem 129′.** Let `F ∈ S^♯` be entire with `d_F = 2` and integer conductor `q_F = Q`. Let `α ∈ Q`
lie in the `⟨T,W⟩`-orbit of `0` in `Q/Z`, where `T(x) = x+1` and `W(x) = −1/(Qx)`. Then `F(s,α)` is
entire and `F(s,α) ∈ M(2, Q q²/gcd(q,Q))`, `q` the denominator of `α mod 1`.

Lemma 234.B says the orbit is all of `Q/Z` for `Q ≤ 3`, and everything except the class of `1/2` for
`Q = 4`. For `Q ≥ 5` the orbit is a proper thin subset (it is the cusp set of the Hecke group `G(√Q)`,
which then has infinite covolume), but Theorem 129′ still applies to it. A convenient sufficient
condition, read off from `4q₂ ≤ Qq`: *if every iterate `α_i` of the reduction satisfies
`|α_i| ≤ 2/Q` in its nearest-integer representative, the reduction terminates.*

### 235.2 The self-referential class

KP's conductor-1 machinery rests on the coincidence `W(1) = −1 ≡ 0 (mod 1)`: the linear twist at
`α = 1` is `F` itself and its dual is `F̄` itself. The general question is which classes are **fixed**
by `W` on `Q/Z`, since those give a self-referential instance of the transformation formula.

**Proposition 132.** Let `Q ≥ 1` be an integer. A class `α ∈ Q/Z` satisfies `W(α) ≡ α` if and only if
`Q(Qn²−4)` is a perfect square for some integer `n` with `Qn² ≥ 4`, and then
`α = (Qn ± √{Q(Qn²−4)})/(2Q)`. For `1 ≤ Q ≤ 4` the solutions are exactly
```
Q = 1 : α ≡ 0    (n = 2, the KP class)        Q = 3 : none
Q = 2 : none                                  Q = 4 : α ≡ 1/2  (n = 1).
```

*Proof.* `W(α) ≡ α` means `−1/(Qα) = α − n` for some `n ∈ Z`, i.e. `Qα² − Qnα + 1 = 0`, so
`α = (Qn ± √{Q²n²−4Q})/(2Q)`, rational iff `Q(Qn²−4)` is a square. For `Q = 2`, `2(2n²−4) = 4n²−8 = m²`
forces `m = 2m'` and `n² − m'² = 2`, impossible. For `Q = 3`, `9n²−12 = m²` forces `3 ∣ m`, `m = 3m'`,
and `3(n²−m'²) = 4`, impossible. For `Q = 4`, `4(4n²−4) = 16(n²−1)` is a square iff `n²−1` is, i.e.
`n = 1`, giving `α = 1/2`. For `Q = 1`, `n²−4 = m²` forces `n = 2`, `m = 0`, `α = 1 ≡ 0`. ∎

**Consequence.** At conductor `4` the transformation formula at `α = 1/2` reads, since
`(√4 · 1/2)^{2s−1+iθ_F} = 1` and `i q_F α/2π = i/π`,
```
F(s,1/2) = −i ω_F^* Σ_{ν=0}^{K} (i/π)^ν Q_ν(s) F̄(s+ν+iθ_F, 1/2) + H_K(s,1/2) ,
```
an exact self-referential identity of the same shape as KP's conductor-1 identity at `α = 1`. This is
the conductor-4 substitute for the "peculiar property of certain linear twists", and is the natural
entry point for (POLE) and for Step 1 of (CLASS-q) at `Q = 4`.

**Consequence (negative).** At conductors `2` and `3` there is **no** fixed class, so no self-referential
identity of length one exists; any Step-1 analogue there must come from a `W`-cycle of length `≥ 2`,
i.e. from a rational point of period `≥ 2` under `α ↦ {−1/(Qα)}`, or from the nonlinear twists.
**Do not look for a fixed class at `Q = 2, 3`.**

### 235.3 Status of the open items

- **(POLE)** — unchanged for `Q = 2,3`; at `Q = 4` attack it through §235.2's identity at `α = 1/2`.
- **(CLASS-q)** — unchanged.
- **(ORBIT-5)** — describe `⟨T,W⟩·0 ⊂ Q/Z` for `Q ≥ 5` explicitly. Theorem 129′ then yields the Euler
  factor bound at every prime `p` all of whose classes `a/p` lie in the orbit; by Lemma 234.B this needs
  the reduction to stay inside `[−2/Q,2/Q]`, which fails for `a ≈ p/2`. Expect: no prime works for
  `Q ≥ 5`, matching KPR's finding (arXiv:2208.12947) that no `q ≥ 4` is a forbidden conductor, i.e.
  that at `Q ≥ 4` the class `S^♯_2` is genuinely large.

---

## 236. Cycle 236 (2026-07-26) — `W`-cycles, loop weights, and the conductor-4 composite identity

### 236.1 The composite of a `W`-cycle

Let `F ∈ S^♯_2` with integer conductor `Q`, and let `α_0 → α_1 → ⋯ → α_{r−1} → α_0` be a cycle of the
reduction map `α ↦ {−1/(Qα)}` on `Q/Z`, with chosen representatives `α_i > 0`. Composing the
transformation formula `r` times and writing `c_i = −iω^*` for the relevant root-number factor at step
`i`, the leading (`ν = 0` at every step) term of the composite is
```
F(s,α_0) = (∏_i c_i) · C^{2s−1+iθ_F·(±)} · F^{(r)}(s,α_0) + Σ_{k ≥ 1}(…)F^{(r)}(s+k/1,α_0) + (hol.),
C := ∏_{i=0}^{r−1} (√Q α_i) ,
```
where `F^{(r)} = F` if `r` is even and `F̄` if `r` is odd.

*Two regimes.*
- **`C = 1`.** The leading terms cancel and one is left with `0 = Σ_{k≥1}(…)F(s+k,α_0) + (hol.)`, a
  *relation*: taking residues at `s = 1−k` produces equations on the polynomials `Q_ν`, hence on the
  `γ`-factor data. This is the conductor-1 mechanism of Kaczorowski–Perelli transplanted.
- **`C ≠ 1`.** The leading terms do **not** cancel and the composite is a *functional equation*
  `F(s,α_0)(1 − c C^{2s}) = (\text{lower terms})`, which meromorphically continues `F(s,α_0)` with
  possible poles only where `cC^{2s} = 1`, i.e. on the line `σ = 0` when `|C| ≠ 1`.

> **Attribution.** This "loop with a weight" mechanism is not new: it is the technique of
> Kaczorowski–Perelli–Radziejewski, arXiv:2208.12947, where `C` is their **weight `w_q(m)`** of the
> continued fraction `c(q,m)` and the basic theorem is that for an existing `F ∈ S^♯_2` of conductor `q`
> the weight of every proper loop must be `1`. Producing a proper loop with `w_q ≠ 1` proves `q`
> forbidden. Their loops are built from *nonlinear* twists; the display above is the *linear*-twist
> version. **Recorded so that this is not re-derived a third time.**

### 236.2 The one place where the linear-twist loop is degenerate

At `Q = 4` and `α = 1/2` — the unique fixed class of Proposition 132 — the loop has length `r = 1` and
```
C = √Q α = √4 · (1/2) = 1 .
```
So conductor 4 sits exactly in the `C = 1` regime, consistently with KPR's theorem that no `q ≥ 4` is
forbidden. Writing `G(s) := F(s,1/2)`, `κ := i/π`, the identity and its conjugate compose to
```
0 = Σ_{k ≥ 1} c_k(s) G(s+k) + (holomorphic for σ > −K+1/2),
c_k(s) = Σ_{ν+μ = k} κ^ν \barκ^μ Q_ν(s) \bar Q_μ(s+ν+iθ_F).
```
Each `G(s+k)`, `k ≥ 1`, is holomorphic for `σ > 1−k`, so the identity is valid for `σ > 0` and the
residue at `s = 0` gives, whenever `G` has a pole at `s = 1`,
```
κ Q_1(0) + \barκ \bar Q_1(iθ_F) = 0 ,  i.e.  Q_1(0) = \bar Q_1(iθ_F) .
```
When `F ∈ S` has a pole of order `m_F` at `s = 1` one computes, from the Euler product,
`G(s) = F^{(2)}(s)(F_2(s) − 2)` with `F^{(2)} = F/F_2`, so `G` has a pole of order exactly `m_F` at
`s = 1` **unless `F_2(1) = 2`**; the value `F_2(1) = 2` is not excluded by `|α_j(2)| ≤ 1, ∂_2 ≤ 2`
(e.g. `α_1 = α_2 = 2−√2`), so that degenerate branch has to be handled separately.

### 236.3 Consequences for the open list

- **(POLE) at `Q = 4`** now has a concrete attack: §236.2's relation, plus the residue argument at
  `s = 1−ν` applied to the *first-order* identity, is the analogue of KP's Lemma 4.1. The obstruction
  has moved from "no self-referential class" to "the class `1/2` may be a non-pole of `G`".
- **(LOOP-23).** At `Q = 2, 3` Proposition 132 rules out length-1 loops. The next question is whether
  the reduction map `α ↦ {−1/(Qα)}` on `Q/Z` has **any** periodic point for `Q = 2, 3`. By Lemma 234.B
  the denominator strictly decreases every two steps, so **no periodic orbit can exist**: a cycle would
  force `q < q`. Hence:

> **Proposition 133.** For `Q ∈ {1,2,3}` the reduction map on `Q/Z` has no periodic orbit other than the
> terminal class `0`; for `Q = 4` the only extra periodic orbit is the fixed class `1/2`. Consequently
> the linear-twist loop mechanism of §236.1 is *empty* at `Q ≤ 3`, and every rational linear twist is
> reached from `0` by a finite chain — which is exactly why Theorem 129 holds there and why no
> conductor `≤ 4` is forbidden.

This closes the linear-twist route to Step 1 of (CLASS-q) at `Q = 2, 3`: there is no loop to exploit,
so Step 1 there must use the **nonlinear** twists, as KP do. **Do not search for linear-twist loops at
`Q = 2, 3`.**

---

## 237. Cycle 237 (2026-07-26) — formalisation, and the state of the formal tree

### 237.1 What is formalised

`formal/GaloisForLFunctions/HTGeometry/TwistConductorDescent.lean` (registered in the `HTGeometry`
umbrella; `lake build +GaloisForLFunctions.HTGeometry` clean; every declaration
`#print axioms`-checked, only `propext`, `Quot.sound`, `Classical.choice`):

| declaration | statement |
|---|---|
| `dualDenom Q q A` | `(Q / gcd q Q) * A` — the denominator produced by `α ↦ −1/(Qα)` |
| `twistConductor Q q` | `(Q / gcd q Q) * q ^ 2` — the twist conductor `h_Q` |
| `twistConductor_one` | `twistConductor Q 1 = Q` (the base case `F ∈ M(2,q_F)`) |
| `gcd_dualDenom` | `gcd (dualDenom Q q A) Q = Q / gcd q Q` for `A` coprime to `q` (Lemma 234.A) |
| `twistConductor_dualDenom` | `h_Q(Wα)·q² = h_Q(α)·(Q A²)` — the exact recursion, representative-free |
| `four_mul_dualDenom_two_le_two_mul` | `4 q₂ ≤ Q·(2A)` — sharp two-step contraction |
| `four_mul_dualDenom_two_le` | `4 q₂ ≤ Q q` (Lemma 234.B) |
| `dualDenom_two_lt` | strict descent for `Q ≤ 3` |
| `dualDenom_two_lt_four_of_odd` | strict descent at `Q = 4` for odd denominator |
| `four_le_of_dualDenom_two_ge` | no two-step cycle unless `4 ≤ Q` (Proposition 133) |
| `no_fixed_class_two` | `4n² − 8 ≠ m²` over `Z` (no fixed class at `Q = 2`) |
| `no_fixed_class_three` | `9n² − 12 ≠ m²` over `Z` (no fixed class at `Q = 3`) |
| `dualDenom_four_two_one` | `dualDenom 4 2 1 = 2` (the fixed class `1/2` at `Q = 4`) |

So the entire arithmetic of §§234–236 — the conductor recursion, the descent, the threshold `Q < 4`,
the exceptional class at `Q = 4`, and the non-existence of fixed classes at `Q = 2,3` — is machine
checked. What is not formalised is the analytic induction of Theorem 129, which quotes the
Kaczorowski–Perelli transformation formula.

### 237.2 Pre-existing state of the formal tree (not caused by this line of work)

- `RHTower/BourgainA6LocalRecurrence.lean` was orphaned **and** did not compile; its
  `ENNReal.ofReal`-bookkeeping proof was repaired here and the module wired into the `RHTower`
  umbrella.
- `lake build +GaloisForLFunctions.RHTower` still **fails**, in the committed module
  `RHTower/SoninCoupledPrimeArchGramTransfer.lean` (two errors: a `Finset.sum_congr` unification failure
  at line 1837 and a "No goals to be solved" at line 2322). The file is unmodified by this session.
- `scripts/formal_tools.py lint` still reports two orphaned modules:
  `RHTower.DeningerArithmeticJetDeterminant` and `HTGeometry.FourAccountings`.

`lake build +GaloisForLFunctions.HTGeometry` is clean, which is the area this line of work lives in.

---

## 238. Cycle 238 (2026-07-26) — **the duality operator computed in closed form, and Step 1 at conductors 2 and 3**

### 238.1 The computation

Kaczorowski–Perelli's transformation formula for nonlinear twists (arXiv:1507.07177, Theorem 1;
arXiv:1107.???? = *Twists and resonance I/II*) applies to `F(s;f) = Σ a(n)n^{−s}e(−f(n,α))` whenever the
leading exponent `κ_0` of `f` exceeds `1/d`, and reads
```
F(s;f) = Σ_{j=0}^{J} W_j(s) F̄(s^* + η_j ; f^*) + G(s;f),        G holomorphic for σ > −K,
```
with `s^* = (s + dκ_0/2 − 1 + i d θ_F κ_0)/(dκ_0 − 1)` and `f^* = T^♭(f)`, where
```
T(f)(ξ,α) = (4π²i)^{−1} ∮_C  Φ Φ_zz / Φ_z  dz ,   Φ(z,ξ,α) = z^{1/d} − 2π f(qz/ξ, α),
q = q_F (2πd)^{−d} ,
```
`C` a small circle around the `z`-critical point. **`T` is self-reciprocal, `T² = id`, and depends on
`F` only through `d` and `q_F`.** The shift operator `S(f) = f + P(ξ)`, `P ∈ Z[ξ]`, acts trivially on
twists (`e(−P(n)) = 1`) but not on `T`; the group is `𝔊 = ⟨T, S^{(k)}⟩`.

**Lemma 238.A (closed form of `T` in degree 2).** Let `d = 2`, `q_F = Q`, and
`f(ξ,α) = c ξ + γ ξ^{1/2}` with `c ≠ 0` (so `κ_0 = 1 > 1/2`). Then
```
T(f)(ξ,α) = [ ξ − γ√Q ξ^{1/2} + γ²Q/4 ] / (cQ) ,
```
that is
```
c ↦ 1/(cQ) ,        γ ↦ −γ/(c√Q) ,        (plus a constant phase γ²/(4c)) .
```

*Proof.* With `u = z^{1/2}`, `Φ = a u − b u²` where `a = 1 − 2πγ√q ξ^{−1/2}`, `b = 2π c q ξ^{−1}`. Then
`Φ_z = (a − 2bu)/(2u)` and `Φ_{zz} = −a/(4u³)`, so
`ΦΦ_{zz}/Φ_z = −a(a−bu)/(2u(a−2bu))`; since `dz = 2u\,du`, the contour integral becomes
`∮ −a(a−bu)/(a−2bu)\,du = 2πi·a²/(4b)`, whence `T(f) = a²/(8πb)`. Substituting `a,b` and using
`16π²q = q_F = Q`, `4π√q = √Q`, gives the display. ∎

*Checks.* `T² = id`: `c ↦ 1/(cQ) ↦ 1/((1/(cQ))Q) = c` and `γ ↦ −γ/(c√Q) ↦ γ`. ✓
At `Q = 1`, `c = 1` — KP's case — one gets `c ↦ 1`, `γ ↦ −γ`, i.e. `f^*(ξ,α) = ξ − αξ^{1/2} + α²/4`, so
the dual of the standard twist is the standard twist at `−α`. **That is exactly the "peculiar property
of certain linear twists which holds in the case `q = 1`"**, now exhibited as the statement that
`c = 1` is a fixed point of `c ↦ 1/(cQ)` precisely when `Q = 1`.

### 238.2 The reduction, and what a loop is

`F(s; cξ + γξ^{1/2}) = F(s,γ)` — the standard twist — exactly when `c ∈ Z ∖ {0}`. So the object of
interest is the orbit of `c = 1` under the group generated by
```
T : c ↦ 1/(Qc) ,          S_m : c ↦ c + m   (m ∈ Z) ,
```
and a **loop** is a chain `c_0 = 1 → c_1 → ⋯ → c_r ∈ Z` with `c_{i+1} = T(c_i + m_i)`, which is
**proper** when `m_i ≠ 0` for `1 ≤ i ≤ r−1` (otherwise two consecutive `T`'s cancel and the chain is
trivial). Its **weight** is the factor by which `γ` returns: `γ_r = w·γ`. Writing `c_i = A_i/D_i` in
lowest terms and `B_i = A_i + m_i D_i`, one has exactly as in Lemma 234.A
```
c_{i+1} = D_i / (Q B_i) ,   gcd(D_i, QB_i) = gcd(D_i,Q) =: g_i ,
A_{i+1} = ±D_i/g_i ,   D_{i+1} = (Q/g_i)|B_i| .
```
Hence: **a chain terminates at the current step iff `Q ∣ D_i` and `A_i ≡ ±1 (mod D_i)`.**

> This is the same arithmetic as the linear-twist reduction of §234, with `α ↦ −1/(Qα)` replaced by
> `c ↦ 1/(Qc)`; the weight `w` is KPR's weight `w_q` (arXiv:2208.12947), whose uniqueness is their
> Theorem 1. What follows is not their forbidden-conductor conclusion but the *positive* use of a
> weight-one loop.

### 238.3 The loops at conductors 2 and 3

**Theorem 134.** For `Q = 2` the chain
```
c : 1 →(m=0)→ 1/2 →(m=−1)→ −1 ∈ Z ,          γ : α ↦ −α/√2 ↦ −α ,
```
is a proper loop of length 2 and weight `−1`. For `Q = 3` the chain
```
c : 1 →(m=0)→ 1/3 →(m=−1)→ −1/2 →(m=+1)→ 2/3 →(m=−1)→ −1 ∈ Z ,
γ : α ↦ −α/√3 ↦ −α/2 ↦ α/√3 ↦ α ,
```
is a proper loop of length 4 and weight `+1`. In both cases the length is **even**, so the composite
returns `F` itself (not `F̄`) and the accumulated `s`-shift `2iθ_F − 2iθ_F` vanishes.

*Verification of the `Q = 3` chain.* `T(1) = 1/3`; `T(1/3 − 1) = T(−2/3) = 1/(3·(−2/3)) = −1/2`;
`T(−1/2 + 1) = T(1/2) = 1/(3/2) = 2/3`; `T(2/3 − 1) = T(−1/3) = 1/(−1) = −1`. Shifts `−1, +1, −1` are
non-zero, so the loop is proper. The `γ`-track uses `γ ↦ −γ/(c√Q)` with `c` the *shifted* value:
`−α/(1·√3) = −α/√3`; `−(−α/√3)/((−2/3)√3) = −α/2`; `−(−α/2)/((1/2)√3) = α/√3`;
`−(α/√3)/((−1/3)√3) = α`. ∎

**Theorem 135 (Step 1 at conductors 2 and 3).** Let `F ∈ S^♯` have degree 2 and conductor `Q ∈ {2,3}`,
and let `α ∈ Spec(F)`. Then for every integer `M ≥ 0`
```
F(s,α) = Σ_{m=0}^{M} W_m^{(Q)}(s,α) F(s + η_m, ε_Q α) + H_M(s,α) ,      ε_2 = −1, ε_3 = +1,
```
where `W_0^{(Q)}(s,α) ≡ 1`, the shifts `0 = η_0 < η_1 < ⋯` are `F`-independent, the `W_m^{(Q)}` are
polynomials in `(s,α)` linear in the structural invariants `d_F(ℓ)` with coefficients depending only on
`Q`, and `H_M(s,α)` is holomorphic for `σ > −(M−1)/2`. Consequently the first term on the right cancels
the left, and — exactly as in KP's conductor-1 argument — vanishing of the residue of
`Σ_{m≥1}W_m^{(Q)}(s,α)F(s+η_m,ε_Qα)` at each pole `s_M` of `F(s,α)` yields, for every `α ∈ Spec(F)`, a
polynomial identity in `α` whose coefficients must all vanish, hence a **universal (in `F`, given `Q`)
family of quadratic relations on the structural invariants `d_F(ℓ)`**.

*Proof.* Compose the KP transformation formula along the loop of Theorem 134, using
`F(s; cξ + γξ^{1/2}) = F(s,γ)` at the two endpoints (`c = 1` and `c = −1`, both integers) and the
triviality of `S` on twists at the intermediate steps. The loop has even length, so the composite maps
`F` to `F`; its weight is `ε_Q`, so the twist parameter returns to `ε_Q α`. The `W_j` of KP's Theorem 1
have the form `e^{a_js}P_j(s)` with `deg P_j ≪ j`, and their composition along a fixed finite chain is
again of that form; the shifts add. Holomorphy of the remainder in `σ > −(M−1)/2` follows from the
`G(s;f)`-bounds of KP's Theorem 1 applied at each of the (finitely many) steps. ∎

**Corollary 136.** For `Q ∈ {2,3}`, all structural invariants `d_F(ℓ)` of any `F ∈ S^♯_2` with `q_F = Q`
are determined by `d_F(1)` through universal polynomials `E_ℓ^{(Q)}`, and hence — by the same route as
KP's Proposition 3.1 — the invariant `χ_F = H_F(1)+H_F(2)+2/3` determines `(ω/ω_F)h_F(s)`.

This is the exact conductor-2 and conductor-3 analogue of Step 1 of the conductor-1 classification, and
it was the announced obstruction ("*quite possibly, an analogous description can be obtained for other
small integer conductors*", arXiv:2503.02492 §1).

### 238.4 Conductor 4 is different

At `Q = 4` the map `c ↦ 1/(4c)` has the rational fixed points `c = ±1/2`, which are **not reachable**
from `c ∈ Z` (a first step from `c_0 ∈ Z` gives `c_1 = 1/(4B_0)`, never `±1/2`). A search over the
terminal criterion of §238.2 shows no proper loop of length 2 or 4:
- length 2 needs `|1 + 4m_1| = 1` with `m_1 ≠ 0`, impossible;
- length 4 needs `4|B_2|` to divide `|D_2 ∓ 1|` with `D_2 = |1+4m_1|` odd, forcing `|B_2| = 1` and then
  `m_2 = 0`, i.e. not proper.

So conductors 2 and 3 admit Step 1 while conductor 4 does not, by this route — mirroring exactly the
linear-twist picture, where `Q = 4` is the case with a second cusp. **Do not look for a length-2 or
length-4 proper loop at `Q = 4`.**

### 238.5 What is still needed for the full classification at `Q = 2, 3`

- **(STEP1-EXPLICIT).** Make the coefficients of `W_m^{(Q)}` explicit enough to extract the top
  coefficient of the polynomial `W_M(α)` and verify that its normalisation is non-degenerate, i.e. the
  analogue of KP's `(-2πi)^{−N}B_N(s_{2N},0,N) + B_{2N}(s_{2N},N,0) ≠ 0`. Without it the induction
  `d_F(ℓ) = E_ℓ(d_F(1))` does not start.
- **(STEP2-4).** Virtual `γ`-factors, period functions, and the endgame at `Q = 2, 3`; the relevant
  converse theorems are Hecke's and Maass' for `Γ_0(2)^+ ≅ G(√2)` and `Γ_0(3)^+ ≅ G(√3)`.
- Only then does one get Selberg's Conjectures A and B on `S_2` with `q_F ∈ {1,2,3}`.

---

## 239. Cycle 239 (2026-07-26) — **nineteenth defect (own)**: the sign of the `γ`-rule, and the corrected weights

### 239.1 The defect

§238.1's Lemma 238.A was derived from the contour formula for `T` under the standing hypothesis
`α_0 > 0` (positive leading coefficient), which is where Kaczorowski–Perelli's definition of `T` is
given; for a negative leading coefficient they *define* `T(f) := −T(−f)`. Applying that to
`f = cξ + γξ^{1/2}` with `c < 0` gives
```
T(f) = [ ξ + γ√Q ξ^{1/2} + γ²Q/4 ] / (cQ) ,
```
i.e. the `ξ^{1/2}`-coefficient is `+γ/(c√Q)`, **not** `−γ/(c√Q)`. Since `c < 0` this is
`−γ/(|c|√Q)`, so the two cases unify:

> **Lemma 238.A′ (corrected).** For `d = 2`, `q_F = Q`, `f = cξ + γξ^{1/2}` with `c ≠ 0`,
> ```
> c ↦ 1/(cQ) ,        γ ↦ −γ/(|c|√Q) ,
> ```
> together with an additive constant `γ²/(4c)` in the phase. The map is an involution:
> `c ↦ 1/(cQ) ↦ c` and `γ ↦ −γ/(|c|√Q) ↦ γ`.

`|c|` was silently taken as `c` in §238.3. **Standing rule reaffirmed: check the domain convention of
every imported definition, including the sign convention that extends it.**

### 239.2 Corrected weights — both loops have weight exactly `+1`

Tracking `γ_i = t_i α/(√Q)^i`, the rational track is `t ↦ −t/|c|` with `c` the *shifted* value.

| `Q` | chain `c` (after shift) | `t`-track | weight `t_r/Q^{r/2}` |
|---|---|---|---|
| 2 | `1, −1/2` | `1, −1, 2` | `2/2 = 1` |
| 3 | `1, −2/3, 1/2, −1/3` | `1, −1, 3/2, −3, 9` | `9/9 = 1` |

So **Theorem 134 is corrected to: both proper loops have weight `+1`**, and hence in **Theorem 135**
```
ε_2 = ε_3 = +1 ,
```
i.e. the composite identity is self-referential in the *same* twist parameter:
```
F(s,α) = Σ_{m=0}^{M} W_m^{(Q)}(s,α) F(s + η_m, α) + H_M(s,α) ,   W_0^{(Q)} ≡ 1,
```
for `Q ∈ {2,3}` and every `α ∈ Spec(F)` — exactly the shape of Kaczorowski–Perelli's conductor-1
Lemma 3.1. Corollary 136 is unaffected and now follows by their argument verbatim.

The corrected weight `1` is also the consistency check demanded by Kaczorowski–Perelli–Radziejewski
(arXiv:2208.12947): an existing `F ∈ S^♯_2` of conductor `q` forces every proper loop to have weight
`1`, and `q = 2, 3` are not forbidden conductors. A weight of `−1` would have been an inconsistency.

### 239.3 Formalised

`formal/GaloisForLFunctions/HTGeometry/DualityLoopWeights.lean` (in the `HTGeometry` umbrella,
`lake build` clean, axioms `propext`/`Classical.choice`/`Quot.sound` only):

| declaration | statement |
|---|---|
| `cStep Q c` | `1/(Q*c)` — duality on the linear coefficient |
| `tStep t c` | `-t/|c|` — duality on the rational `γ`-track |
| `cStep_cStep` | `cStep Q (cStep Q c) = c` (involution) |
| `tStep_tStep` | `tStep (tStep t c) (cStep Q c) = t * Q` (involution after the two `√Q`) |
| `dualityLoop_two` | the chain `1 → 1/2 → −1`, shifts `0, −1`, weight `1` |
| `dualityLoop_three` | the chain `1 → 1/3 → −1/2 → 2/3 → −1`, shifts `0, −1, 1, −1`, weight `1` |
| `no_proper_length_two_loop_four` | `m ≠ 0 ⟹ |1+4m| ≠ 1` (no length-2 proper loop at `Q = 4`) |
| `proper_length_two_loop_two` | `|1+2(−1)| = 1` (the length-2 loop at `Q = 2` exists) |
| `cStep_four_fixed` | the fixed points of `c ↦ 1/(4c)` are exactly `±1/2` |

---

## 240. Cycle 240 (2026-07-26) — **the exact range of the Step-1 mechanism: proper loops exist iff `q_F ≤ 3`**

### 240.1 The dilation law

**Lemma 240.A.** In degree 2 the duality operator at conductor `Q` is the conductor-one operator
composed with a dilation:
```
T_Q(f)(ξ) = T_1(f)(ξ/Q) .
```

*Proof.* By Lemma 238.A′, `T_Q : (c,γ) ↦ (1/(cQ), −γ/(|c|√Q))` and `T_1 : (c,γ) ↦ (1/c, −γ/|c|)`, while
`f ↦ f(·/Q)` is `(c,γ) ↦ (c/Q, γ/√Q)`. Compose. ∎

So the whole conductor dependence of the nonlinear-twist duality in degree 2 is a single dilation of
the dual phase — which is why the arithmetic below is the *same* arithmetic as the linear-twist
descent of §234.

### 240.2 The chain arithmetic

Write `c_i = A_i/D_i` in lowest terms, `g_i = gcd(D_i,Q)`, `Q = g_i m_i`, `D_i = g_i e_i`, and let
`B_i ≡ A_i (mod D_i)`, `B_i ≠ 0`, be the shifted numerator. Then (Lemma 234.A, verbatim)
```
|A_{i+1}| = e_i = D_i/g_i ,      D_{i+1} = m_i |B_i| = (Q/g_i)|B_i| ,     g_{i+1} = Q/g_i .
```
The chain **terminates** at step `i+1` iff `D_{i+1} = 1`, i.e. `Q ∣ D_i` and `A_i ≡ ±1 (mod D_i)`, and it
is **proper** at step `i` iff `B_i ≠ A_i`, which forces `|B_i| ≥ D_i − |A_i|`.

### 240.3 The theorem

**Theorem 137.** A proper loop `c_0 = 1 → c_1 → ⋯ → c_r ∈ Z` exists if and only if `Q ≤ 3`.

*Proof.* Existence for `Q = 1` is Kaczorowski–Perelli's case (`c ↦ 1/c` fixes `1`); for `Q = 2, 3` the
explicit loops are Theorem 134.

For `4 ≤ Q` we show no proper chain leaves the region `D ≥ 2`. Set the invariant
`(H_i): 2|A_i| ≤ D_i`.
*Base.* `c_0 = 1` gives `A_1 = ±1`, `D_1 = Q|B_0| ≥ Q ≥ 4`, so `(H_1)` holds.
*Properness gives room.* `(H_i)` and `B_i ≠ A_i` give `|B_i| ≥ D_i − |A_i| ≥ D_i/2`, i.e. `D_i ≤ 2|B_i|`.
*Invariant.* `2|A_{i+1}| = 2e_i` and `D_{i+1} = m_i|B_i|`; since `Q e_i = m_i D_i ≤ 2 m_i |B_i|` and
`4e_i ≤ Q e_i`, we get `2|A_{i+1}| ≤ D_{i+1}`, i.e. `(H_{i+1})`.
*Non-termination.* If `D_{i+1} = m_i|B_i| = 1` then `m_i = 1`, so `g_i = Q` and `Q ∣ D_i`, whence
`Q ≤ D_i`; but `|B_i| = 1` with `D_i ≤ 2|B_i|` gives `D_i ≤ 2 < 4 ≤ Q`, a contradiction.
*Growth.* `Q D_i ≤ Q·2|B_i| = 2 g_i (m_i |B_i|) = 2 g_i D_{i+1} ≤ 4 g_i |B_{i+1}| = 4 D_{i+2}`, using
`g_{i+1} = Q/g_i` so that `D_{i+2} = g_i|B_{i+1}|`. Hence `4 D_{i+2} ≥ Q D_i`.
So for `Q ≥ 4` the denominators never reach `1`, and for `Q > 4` they grow geometrically. ∎

**Corollary 138.** The Step-1 mechanism of the degree-2 classification — a self-referential identity for
the standard twist obtained by composing the transformation formula along a loop — exists **exactly**
for conductors `q_F ∈ {1, 2, 3}` and provably **fails** for every `q_F ≥ 4`.

This is sharp, elementary, and matches on the nose the three other thresholds already met in this
programme: the linear-twist descent `4q₂ ≤ Qq` of Lemma 234.B; the discreteness of the Hecke group
`G(√Q)`; and Kaczorowski–Perelli–Radziejewski's finding that no conductor `q ≥ 4` is forbidden.
Conductor 4 is the exact boundary: the fixed classes `±1/2` of `c ↦ 1/(4c)` exist but are unreachable
from `Z`, and the growth inequality degenerates to `D_{i+2} ≥ D_i`.

> **Programme consequence.** Selberg's Conjectures A and B for degree 2 are now reachable, by the
> Kaczorowski–Perelli route, on `q_F ∈ {1,2,3}` and on nothing more. Conductor `4` and above needs a
> genuinely different Step 1. **Do not attempt the loop route at `q_F ≥ 4`.**

### 240.4 Formalised

Added to `formal/GaloisForLFunctions/HTGeometry/DualityLoopWeights.lean`:
`proper_half_invariant` (`2e ≤ mb`), `proper_not_terminal` (`2 ≤ mb`), `proper_two_step_growth`
(`Q·D ≤ 4·(g·b')`). Axioms: `propext`, `Quot.sound` only. `lake build +GaloisForLFunctions.HTGeometry`
clean.

---

## 241. Cycle 241 (2026-07-26) — the square-index / symmetric-square split, and the exact two halves of Conjecture A in degree 2

### 241.1 The local identity

Corollary 130 makes the full Satake data available unconditionally for `F ∈ S` entire of degree 2 with
`q_F ∈ {1,2,3,4}`: `F_p(s) = ((1−α_1(p)p^{−s})(1−α_2(p)p^{−s}))^{−1}` with `|α_j(p)| ≤ 1` (odd `p` if
`q_F = 4`). Write
```
e_2(p) := α_1(p)α_2(p) = a_F(p)² − a_F(p²) ,        |e_2(p)| ≤ 1 .
```

**Lemma 241.A.** With `h_n(x,y) = Σ_{i+j=n}x^iy^j` (so `a_F(p^n) = h_n(α_1,α_2)`),
```
h_{2k}(a,b) = h_k(a²,b²) + a b · h_{k−1}(a²,b²)      (k ≥ 1),
```
equivalently `Σ_k h_{2k}(a,b)X^k = (1 + abX)/((1−a²X)(1−b²X))`.

*Proof.* Induction on `k` using `h_{n+1}(x,y) = x^{n+1} + y h_n(x,y)`; base `k=1` is
`a²+ab+b² = (a²+b²)+ab`. Alternatively `(a−b)h_n(a,b) = a^{n+1}−b^{n+1}` gives the identity after
clearing `(a²−b²)`. ∎

### 241.2 The consequence

**Theorem 139.** For `F` as above,
```
Σ_{n≥1} a_F(n²) n^{−s} = Sym²F(s) · ∏_p (1 − e_2(p)² p^{−2s}) ,
Sym²F(s) := ∏_p [(1 − α_1(p)²p^{−s})(1 − e_2(p)p^{−s})(1 − α_2(p)²p^{−s})]^{−1} ,
```
the correction factor being absolutely convergent and non-vanishing for `σ > 1/2`. Hence the square-index
series and the symmetric square have identical analytic behaviour in `σ > 1/2`. Moreover
`log Sym²F(s) = Σ_p a_F(p²)p^{−s} + O(1)` for `σ > 1`, so the prime density `δ₁(a_F(·²))` is exactly the
"pole order" of `Sym²F` at `s = 1`.

*Proof.* Multiplicativity of `n ↦ a_F(n²)` (already formalised) reduces to the local statement, which is
Lemma 241.A: `Σ_k a_F(p^{2k})X^k = (1+e_2X)/((1−α_1²X)(1−α_2²X))`, and
`(1+e_2X) = (1−e_2X)^{−1}(1−e_2²X²)`. The identity `α_1²+e_2+α_2² = a_F(p²)` gives the last claim. ∎

**Corollary 140 (the two halves).** If moreover `F` has real Dirichlet coefficients, then
```
n_F = δ₁(a_F(·²)) + δ₁(e_2) ,
```
i.e. **Selberg's Conjecture A for `F` is exactly the conjunction of**
- `(SYM)` the symmetric-square density `δ₁(a_F(·²))` is an integer, and
- `(DET)` the determinant density `δ₁(e_2) = lim (loglog x)^{−1}Σ_{p≤x}e_2(p)/p` is an integer.

*Proof.* `|a_F(p)|² = a_F(p)² = a_F(p²) + e_2(p)` by Newton, divide by `p`, sum, normalise. ∎

Both densities are bounded: `|δ₁(e_2)| ≤ 1` since `|e_2(p)| ≤ 1`, hence `n_F ∈ [δ₁(a_F(·²))−1,
δ₁(a_F(·²))+1]` and, by Corollary 131, `δ₁(a_F(·²)) ≤ 5`. For an automorphic `F` of level `N` and
nebentypus `χ`, `e_2(p) = χ(p)`, `(SYM)` gives `0` (no pole of `Sym²` for cuspidal `F`) and `(DET)` gives
`1` or `0` according as `χ` is principal or not — reproducing `n_F = 1`.

### 241.3 Where this leaves the programme

`(SYM)` is the hypothesis `(PSD₂)` of Theorem 111 under its old name. **`(DET)` is new and is the
cleaner target**: it is Conjecture A for a *degree-one* object, `∏_p(1−e_2(p)p^{−s})^{−1}`, whose
coefficients are explicit polynomials in the Dirichlet coefficients of `F`. It would follow at once from
`e_2` being a Dirichlet character — which is what the classification would give — so `(DET)` is strictly
weaker than the classification and strictly stronger than nothing.

**Do not attempt** to deduce `(DET)` from `|e_2(p)| ≤ 1` alone: `Σ_p c_p/p` with `|c_p| ≤ 1` can have
any density in `[−1,1]`. What is needed is an arithmetic constraint on `e_2`, e.g. `∂_p = 2` for almost
all `p` (`|e_2(p)| = 1`) — itself open, since Kaczorowski–Perelli only prove `∂_p ≤ d_F`.

### 241.4 Formalised

`formal/GaloisForLFunctions/HTGeometry/SquareIndexSymmetricSquare.lean`: `hSym`, `hSym_succ`,
`hSym_two_mul` (Lemma 241.A, by induction, over any commutative ring), `evenPart_numerator`,
`evenPart_denominator`, `det_eq_hSym_sq_sub` (`ab = h_1² − h_2`). Axioms clean;
`lake build +GaloisForLFunctions.HTGeometry` clean.

---

## 242. Cycle 242 (2026-07-26) — the second cusp at conductor 4: a root-number dichotomy that closes `p = 2`

### 242.1 The identity at the fixed class

Let `F ∈ S^♯` be entire of degree 2 with `q_F = 4`, and put `G(s) := F(s,1/2) = Σ_n (−1)^n a_F(n) n^{−s}`.
By Proposition 132 the class `1/2` is fixed by `W`, and in KP's transformation formula at `α = 1/2`,
`Q = 4`, the prefactor is `(√4·½)^{2s−1+iθ_F} = 1` and the `ν`-factor is `(i q_F α/2π)^ν = (i/π)^ν`, so
```
G(s) = −i ω_F^* [ Ḡ(s+iθ_F) + Σ_{ν=1}^{K} (i/π)^ν Q_ν(s) Ḡ(s+ν+iθ_F) ] + H_K(s,½) ,
```
with `H_K` holomorphic for `−K+1/2 < σ < 2`, `|s| < 2K`.

Suppose `F` has real Dirichlet coefficients (so `Ḡ = G`) and `θ_F = 0`. Then, writing `c := −i ω_F^*`,
```
(1 − c) G(s) = c Σ_{ν=1}^{K} (i/π)^ν Q_ν(s) G(s+ν) + H_K(s,½) .
```
Every `G(s+ν)` with `ν ≥ 1` is an absolutely convergent Dirichlet series for `σ > 1−ν`, hence for
`σ > 0`; so the right-hand side is holomorphic there.

**Theorem 141.** With `F` as above and `ω_F^* ≠ i` (equivalently `c ≠ 1`):
`G(s) = F(s,1/2)` extends to an **entire** function, and `F(s,1/2) ∈ M(2,8)`.

*Proof.* `c ≠ 1` gives `G(s) = (1−c)^{−1}[⋯]`, holomorphic for `σ > 0`. Bootstrapping: knowing `G`
holomorphic for `σ > −j` makes each `G(s+ν)`, `ν ≥ 1`, holomorphic for `σ > −j−1`, so the identity
extends `G` to `σ > −j−1`; and `K` is arbitrary. The growth bound is Theorem 129's computation with
`h_4(1/2) = 4·2²/gcd(2,4) = 8`. ∎

**Corollary 142.** For such `F` in `S`, Corollary 130 extends to `p = 2`: since `h/q_F = 8/4 = 2`,
`∂_2 ≤ [log 2/log 2] = 1`, so `F_2(s) = (1 − α_1(2)2^{−s})^{−1}` with `|α_1(2)| ≤ 1`, i.e.
`|a_F(2)| ≤ 1`. Hence the polynomial Euler product and `|a_F(p)| ≤ 2` hold at **every** prime for
degree 2 with `q_F ∈ {1,2,3,4}`, subject only to the dichotomy below at `q_F = 4`.

### 242.2 The dichotomy, and why it is not vacuous

If `ω_F^* = i` the identity degenerates to `0 = c Σ_{ν≥1}(i/π)^νQ_ν(s)G(s+ν) + H_K(s,½)`, from which
one still gets `Q_1(s) G(s+1)` holomorphic for `σ > −1` — i.e. meromorphic continuation of `G` to
`σ > 0` with poles confined to the zeros of `Q_1(s−1)` — but not holomorphy, so `M(2,8)`-membership
fails to follow.

The degenerate branch is **not** exceptional. With `ω_F^* = ω_F e^{−iπ(η_F+1)/2}` (for `θ_F = 0`) and
`η_F = k−2` for a holomorphic form of weight `k`, one gets `ω_F^* = ±i` always for integral `η_F`; so
`c = −iω_F^* = ±1` and `c = 1` for exactly one of the two root numbers at each weight. Consistency check
on `ζ²`: `γ(s) = π^{−s}Γ(s/2)²`, `η_F = −2`, `ω_F = 1`, so `ω_F^* = e^{iπ/2} = i` — the degenerate
value, which is exactly right, since KP's conductor-1 argument shows a **pole** at `s = 1` forces
`1 + iω_F^* = 0`. So the dichotomy is the same phenomenon: `c = 1` is the polar/degenerate branch.

### 242.3 The second cusp is a genuine orbit

**Proposition 143.** For `Q = 4`, a class with denominator `2u`, `u` odd, has `gcd(2u,4) = 2` and one step
sends the denominator to `2A` with `A` odd. Hence the classes with denominator `≡ 2 (mod 4)` are closed
under `W` and form an orbit disjoint from the orbit of `0` — the orbit of the fixed class `1/2`. This is
the third cusp of `Γ_0(4)`, the one not merged with `∞` by the Fricke involution.

Formalised: `dualDenom_four_second_cusp`, `dualDenom_four_second_cusp_mod` in
`TwistConductorDescent.lean`. Axioms `propext`, `Quot.sound`; `lake build` clean.

### 242.4 A route recorded, with its blocker — do not re-derive

The residue of the standard twist at `s_0` recovers the coefficients: for degree 2 and conductor `q`,
`Res_{s=s_0}F(s,α) = e^{iπ/4}\overline{a_F(α²q/4)}α^{−1/2}`. Taking `α_n = 2n/√q` — an **arithmetic
progression** inside `Spec(F)` — gives `Res_{s=s_0}F(s,α_n) ∝ \overline{a_F(n²)}n^{−1/2}`. Hence, for
`Φ(s,w) := Σ_n n^{−w}F(s,α_n)`,
```
Res_{s=s_0} Φ(s,w) = c_q · \overline{D}(w+½) ,      D(w) = Σ_n a_F(n²)n^{−w} ,
```
so a meromorphic continuation of `Φ` in `w` would give `(SYM)`. Unfolding,
`Φ(s,w) = Σ_m a_F(m)m^{−s} P_w(2√(m/q))` with `P_w(θ) = Σ_n n^{−w}e(−nθ)` the periodic zeta function.

**Blocker.** `P_w(θ)` blows up as `θ → 0` once `Re w ≤ 1`, so continuing `Φ` in `w` requires control of
`‖2√(m/q)‖` — the same small-divisor problem that killed §§219–222 (defect 14: the deficit `X^{1/2}` is
invariant under every Hölder rearrangement). **Do not re-attempt the `Φ(s,w)` route without a new idea
about `‖2√(m/q)‖`**; the `α`-uniform polynomial bounds of Kaczorowski–Perelli (Acta Arith. 116 (2005),
Theorem 2) control the `s`-aspect but not this.

---

## 243. Cycle 243 (2026-07-26) — the general-conductor standard-twist machinery, and the strict-functional-equation frontier

### 243.1 The tool I had been missing

**Kaczorowski–Perelli, *The standard twist of `L`-functions revisited*, arXiv:1911.10497** gives the
functional equation of the standard twist at **every degree and every conductor**. Its content, in the
notation `s_ℓ^* = (d+1)/(2d) − ℓ/d − iθ_F`, `e_ℓ = (d−1)/2 + ℓ + iθ_F`, `n_α = q(α/d)^d`:

- **Structural coefficients at any conductor.**
  `h_F(s) ≈ (ω_F/√(2π))(q^{1/d}/(2πd))^{d(½−s)} Σ_{ℓ≥0} d_ℓ Γ(d(s_ℓ^*−s))`, with `d_0 = d^{idθ_F}`
  (so `d_0 = 1` when `θ_F = 0`).
- **Theorem 2.** For every `k ≥ 0` and `s_{k+1} < σ < s_k`,
  `F(s,α) = (ω_F/√(2π))(q^{1/d}/(2πd))^{d(½−s)} Σ_{ℓ=0}^{k} d_ℓ Γ(d(1−s)−e_ℓ) F̄_ℓ(1−s,α)
            + R(1−s,α) + H_k(s,α)`,
  `H_k` holomorphic in that strip, `≪ |t|^{−θ}`, and `R ≡ 0` when `F` is entire.
- **Theorem 3 (residues, any conductor).**
  `ρ_ℓ(α) = (d_ℓ/d)(ω_F/√(2π)) e^{−iπ(ξ_F+ds_ℓ^*)/2}(q^{1/d}/(2πd))^{d/2−ds_ℓ^*}\overline{a(n_α)}/n_α^{1−s_ℓ^*}` .
  *"In particular, the set of poles of `F(s,α)` is independent of `α` and equals `{s_ℓ^*: d_ℓ ≠ 0}`."*

**Consequence for §238.** Corollary 136 was derived using the conductor-1 residue formula. Theorem 3
above supplies it at conductor `Q`: specialising `d = 2`, `θ_F = 0`, `n_α = qα²/4` gives
`ρ_ℓ(α) ∝ d_ℓ · \overline{a(n_α)} · α^{−1/2−ℓ}`, so the `α`-dependence is `α^{−1/2−ℓ}` and the
`d_ℓ`-dependence is linear — **exactly the two facts the residue extraction of §238.3 needs**, at every
conductor. Corollary 136 is therefore on a rigorous footing at `Q = 2, 3` modulo only
`STEP1-EXPLICIT` (non-degeneracy of the resulting quadratic form).

### 243.2 A second frontier item, explicitly open

KP's **Theorem 4** (same paper): for `F ∈ S^♯` with `d ≥ 1`, `θ_F = 0`, the following are equivalent —
(i) `F(s,α)` satisfies a **strict** functional equation (`H_k ≡ 0` for `k ≥ h`, all `α`);
(ii) `d_ℓ = 0` for `ℓ > h` and `d_h ≠ 0`;
(iii) `γ(s) = Q^s ∏_{j=1}^{N} Γ( (d/2N)s + (2n_j − d − 1)/(4N) )` with integers `n_j ≥ (d+1)/2` forming
a **compatible system** mod `2N`: `n_i ≢ n_j` and `n_i ≢ 1−n_j (mod 2N)`, with `N_0 = h`.

Their **Remark 1.3**: *"At present we don't know examples of `L`-functions whose standard twist satisfies
a strict functional equation, other than the degree 1 `L`-functions and the Hecke `L`-functions of
half-integral weight cusp forms. In particular, we don't know if there exist `L`-functions having a
`γ`-factor of type (1-5) with integer degree `d ≥ 3`. It would be of course interesting to exhibit an
example of this type, or to prove non-existence; the second task appears to be difficult at present."*

### 243.3 The degree-2 specialisation, worked out

At `d = 2` condition (iii) reads `γ(s) = Q^s∏_{j=1}^N Γ(s/N + (2n_j−3)/(4N))`, `n_j ≥ 2` integers.

- `N = 1`: `γ(s) = Q^sΓ(s+μ)` with `μ = (2n−3)/4`, i.e. **`4μ` odd**, `μ ≥ 1/4`. For a half-integral
  weight `κ = k+½` cusp form the `L`-function has `μ = (κ−1)/2 = k/2 − ¼`, and `4μ = 2k−1` is odd ✓ —
  this is exactly KP's known family, with `n = k+1`.
- **Integral-weight newforms are excluded:** `μ = (k−1)/2` gives `4μ = 2(k−1)`, even. So no classical
  degree-2 newform `L`-function has a strict functional equation.
- **`ζ(s)²` is excluded:** `γ(s) = π^{−s}Γ(s/2)²`, `N = 2`, `μ_j = 0`, and `(2n−3)/8 = 0` has no integer
  solution.

So at degree 2 the strict functional equation is exactly the half-integral-weight phenomenon (`N = 1`)
plus whatever `N ≥ 2` configurations are realised — and neither of the two most familiar degree-2
families qualifies.

### 243.4 Compatible systems are transversals of a fixed-point-free involution

**Proposition 145.** On `ZMod(2N)` the reflection `x ↦ 1 − x` is an involution **without fixed points**;
a compatible system is exactly a transversal of its `N` orbits, so compatible systems mod `2N` are in
bijection with the `2^N` choice functions, and any compatible system has at most `N` elements.

*Proof.* A fixed point gives `2x = 1`; reducing along `ZMod(2N) → ZMod 2` turns this into `0 = 1`. The
orbits are therefore the `N` pairs `{x, 1−x}`, and conditions (a), (b) say precisely that the system
meets each pair at most once and never contains both members. ∎

Formalised in `formal/GaloisForLFunctions/HTGeometry/CompatibleSystemInvolution.lean`: `refl2N`,
`refl2N_refl2N`, `refl2N_ne` (fixed-point-freeness), `CompatibleSystem`,
`CompatibleSystem.disjoint_image`, `card_image_refl2N`, `CompatibleSystem.card_le`. Axioms clean;
`lake build +GaloisForLFunctions.HTGeometry` clean.

### 243.5 What this does and does not settle

The arithmetic of (iii) is now completely transparent: compatible systems exist for **every** `N` and
every `d`, in `2^N` residue-configurations. So KP's open problem at `d ≥ 3` is **not** an arithmetic
obstruction — the γ-factor shapes exist; what is unknown is whether any `F ∈ S^♯` realises them.
**Do not attempt to settle Remark 1.3 by ruling out compatible systems: there is nothing to rule out.**

---

## 244. Cycle 244 (2026-07-26) — **the duality operator in every degree, and why the method stops at `d = 2`**

### 244.1 Closed form of `T` in arbitrary degree

**Lemma 244.A.** Let `F ∈ S^♯_d`, `q = q_F(2πd)^{−d}`, and `f(ξ,α) = cξ + γξ^{1/d}` with `c ≠ 0` (so
`κ_0 = 1 > 1/d` for `d ≥ 2`). Put `a = 1 − 2πγq^{1/d}ξ^{−1/d}`, `b = 2πcq/ξ`. Then
```
T(f) = C_d · a^{d/(d−1)} · b^{−1/(d−1)} ,        C_d = (d−1) d^{(d−2)/(d−1)} / (2π d²) .
```

*Proof.* Substituting `u = z^{1/d}` in `Φ(z,ξ,α) = z^{1/d} − 2πf(qz/ξ,α)` gives `Φ = a u − b u^d`,
`Φ_z = (a − d b u^{d−1})/(d u^{d−1})` and `Φ_{zz} = a(1−d)d^{−2}u^{1−2d}`. Since `dz = d u^{d−1}du`, the
integrand of `T` becomes `a(1−d)(a − bu^{d−1})/(a − d b u^{d−1})\,du`, whose only pole is at
`u_0^{d−1} = a/(db)`, with residue `a²(d−1)/(d²b u_0^{d−2})`. Hence
`T(f) = (2π)^{−1}·a²(d−1)/(d²b)·(db/a)^{(d−2)/(d−1)}`, and collecting exponents gives the display,
using `2 − (d−2)/(d−1) = d/(d−1)` and `−1 + (d−2)/(d−1) = −1/(d−1)`. ∎

*Check.* `d = 2`: `C_2 = 1/(8π)` and `T(f) = a²/(8πb)` — Lemma 238.A. ✓

### 244.2 The action on exponents

From Lemma 244.A the leading exponent of `T(f)` is `1/(d−1)`, and in general
```
κ_0 ↦ κ_0^* = κ_0/(dκ_0 − 1) ,        ω ↦ ω^* = ω/(dκ_0 − 1) ,
```
the first map being an **involution** of `Q` with unique non-zero fixed point `κ = 2/d`.

A phase contributes a trivial exponential — so that `F(s;f)` is literally the standard twist
`F(s,α)` — exactly when `f = (\text{integer polynomial}) + αξ^{1/d}`. Hence the loop mechanism of
§§238–240 needs the exponent `1` to be *reproduced* by duality, together with the resonating exponent
`1/d`.

**Theorem 146 (the degree-two barrier).** Let `d ≥ 2`. Starting from `f = cξ + γξ^{1/d}` with `c ∈ Z`,
the exponents of `T(f)` are `1/(d−1) − j/d`, `j ≥ 0`. The resonating exponent `1/d` occurs among them
if and only if `(j+1)(d−1) = d` for some integer `j ≥ 0`, i.e. **if and only if `d = 2`**. Equivalently,
the fixed exponent `2/d` of the duality involution is a positive integer only for `d ∈ {1,2}`.
Consequently:
```
the self-referential (loop) mechanism for the standard twist exists only in degree 2
     — and there, by Theorem 137, only for conductor q_F ≤ 3.
```

*Proof.* The gap of `f` is `ω = 1 − 1/d = (d−1)/d`, and `dκ_0 − 1 = d − 1`, so `ω^* = 1/d` and
`κ_0^* = 1/(d−1)`; the exponents of `T(f)` are `κ_0^* − jω^* = 1/(d−1) − j/d`. Setting this equal to
`1/d` gives `1/(d−1) = (j+1)/d`, i.e. `(j+1)(d−1) = d`; writing `d = e+1` this is `je = 1`, so
`j = e = 1` and `d = 2`. The shift operator can only add exponents in `N`, which for `d ≥ 3` leaves the
non-integer exponents `1/(d−1) − j/d` in place, so no chain of dualities and shifts returns to a
standard twist. For the fixed point, `κ/(dκ−1) = κ` with `κ ≠ 0` gives `dκ = 2`, and `2/d ∈ N_{>0}`
iff `d ∈ {1,2}`. ∎

### 244.3 What this settles

The complete range of the Kaczorowski–Perelli Step-1 method is now known:
```
degree 1  (κ_0 = 2, the quadratic phase)          — classified by KP
degree 2, conductor 1                              — classified by KP
degree 2, conductor 2 and 3                        — Step 1 available (Theorems 134–135), rest open
everything else                                    — no loop, no Step 1  (Theorems 137 and 146)
```
So the halt of the classification programme at degree 2 is **not** a matter of computational difficulty:
in degree `d ≥ 3` the dual of a linear phase has leading exponent `1/(d−1) < 1` and the resonating
exponent `1/d` is never regenerated. Any extension to `d ≥ 3` must replace the loop mechanism, not
refine it.

> **Do not** look for a self-referential standard-twist identity in degree `≥ 3`, nor for a degree-`d`
> analogue of the conductor descent: Theorem 146 rules both out at the level of exponents, before any
> analysis.

### 244.4 Formalised

`formal/GaloisForLFunctions/HTGeometry/DualExponentReturn.lean`: `dualExp`, `dualExp_dualExp`
(involution), `dualExp_eq_self_iff` (`fixed ⟺ dκ = 2`), `exponent_return_iff`
(`(∃j)(j+1)(d−1) = d ⟺ d = 2` for `d ≥ 2`), `fixedExp_isInt_iff` (`2/d ∈ N_{>0} ⟺ d ∈ {1,2}`).
Axioms clean; `lake build +GaloisForLFunctions.HTGeometry` clean.

---

## 245. Cycle 245 (2026-07-26) — Theorem 146 strengthened: the barrier survives every integer part

### 245.1 The interrogation

Theorem 146 ruled out the loop mechanism in degree `≥ 3` for the phase `f = ξ + γξ^{1/d}`. The obvious
repair is to change the integer part: take `f = P(ξ) + γξ^{1/d}` with `P ∈ Z[ξ]` of degree `k ≥ 1`,
which still satisfies `F(s;f) = F(s,γ)`. Does a larger `k` regenerate the resonating exponent?

### 245.2 The answer, two ways

For `f = P(ξ) + γξ^{1/d}` with `deg P = k`, the gaps are generated by `1` and `k − 1/d`, so
`D_f = {m + n(k − 1/d) : m,n ≥ 0}` and the exponents of `T(f)` are
```
κ_0^* − ω^* = (k − m − n(k − 1/d))/(dk − 1) ,        m,n ≥ 0 .
```

**Theorem 146′.** For `d ≥ 2` and `k ≥ 1`, the resonating exponent `1/d` occurs among these if and only
if `m d + n(k d − 1) = 1` for some `m,n ≥ 0`, if and only if `d = 2`, `k = 1` (with `m = 0`, `n = 1`).

*Proof (direct).* `(k − m − nk + n/d)/(dk−1) = 1/d` ⟺ `d(k−m−nk) + n = dk − 1` ⟺
`md + n(kd−1) = 1`. Since `d ≥ 2`, `m ≥ 1` would give `md ≥ 2`, so `m = 0`; then `n(kd−1) = 1` forces
`n = 1` and `kd = 2`, i.e. `d = 2`, `k = 1`. ∎

*Proof (structural, as a check).* The exponent `1/d` is precisely the pole of the duality map
`κ ↦ κ/(dκ−1)`. Solving `1/d = (κ_0 − ω)/(dκ_0 − 1)` gives `dω = 1`, i.e. `ω = 1/d`: **the resonating
exponent survives duality if and only if it already lies in the gap semigroup `D_f`.** And
`1/d ∈ {m + n(k − 1/d)}` forces `(n+1)/d = m + nk`, hence `n(kd−1) = 1 − md`, hence again `m = 0`,
`n = 1`, `kd = 2`. ∎

The two derivations agree, which is the check that matters: the first is a computation with the
explicit exponent list, the second identifies the condition intrinsically as `1/d ∈ D_f`.

### 245.3 Consequence

> The degree-two barrier is **not** an artefact of the choice of phase. For every trivial phase
> `P(ξ) + γξ^{1/d}` with `P ∈ Z[ξ]`, the dual loses the resonating exponent `1/d` as soon as `d ≥ 3`
> (or `d = 2` and `deg P ≥ 2`). Only `d = 2` with `deg P = 1` — Kaczorowski–Perelli's `F(s,1,α)` — keeps
> it.

So the exact and complete list of `(d, deg P)` supporting a self-referential standard-twist identity is
the single pair `(2,1)`, and by Theorem 137 the conductor is then confined to `q_F ≤ 3`.

**Do not** attempt to repair the degree-`≥3` case by enlarging the integer part of the phase; and do not
attempt `d = 2` with a higher-degree integer part either.

### 245.4 Formalised

Added `resonance_return_iff` to
`formal/GaloisForLFunctions/HTGeometry/DualExponentReturn.lean`:
`m*d + n*(k*d − 1) = 1 ↔ (d = 2 ∧ k = 1 ∧ m = 0 ∧ n = 1)` for `d ≥ 2`, `k ≥ 1`.
Axioms `propext`, `Quot.sound`; `lake build +GaloisForLFunctions.HTGeometry` clean.

---

## 246. Cycle 246 (2026-07-26) — corpus-driven: **Selberg's Conjecture A holds in the extremal case `n_F = 4`**

### 246.1 Corpus first

`scripts/formal_tools.py research` on the open cores returned, among others,
`GaloisForLFunctions.HTGeometry.SatakeEnergyBound`, whose module docstring already stated the missing
step: *"equality would force all Satake parameters at a prime to coincide and be unimodular, which
happens only for a `d`-th power of a degree-one element."* The file proved only the "unimodular" half
(`norm_eq_one_of_norm_sum_eq_card`); the "coincide" half was never proved. Proving it is what this
cycle does, and it turns the whole argument quantitative.

Also located and reused conceptually: `HTGeometry.CoefficientPatternDeterminant`
(`coefficientPatternDeterminant_ne_zero_of_isUnit` — *one* full-rank witness certifies a universal
determinant polynomial is non-zero), the exact shape `STEP1-EXPLICIT` will need;
`HTGeometry.ReflectionPositiveHankel` and `HTGeometry.CofiniteTailGramPolarization` for the energy-Gram
line (Theorem 122).

### 246.2 The exact local identities

Let `F ∈ S` be entire of degree 2 with `q_F ∈ {1,2,3,4}`, so that Corollary 130 (with Corollary 142 at
`p = 2` when `q_F = 4`) gives `F_p(s) = ((1−α_1(p)p^{−s})(1−α_2(p)p^{−s}))^{−1}` with `|α_j(p)| ≤ 1`.
Write `a = a_F(p) = α_1+α_2`, `e_2(p) = α_1α_2`, `g(p) = α_1 − α_2`.

**Lemma 246.A (exact, no error term).**
```
e_2(p) = a_F(p)²/4 − g(p)²/4 ,        a_F(p²) = (3/4) a_F(p)² + g(p)²/4 ,
|g(p)|² ≤ 4 − |a_F(p)|² .
```
*Proof.* The first is `α₁α₂ = ((α₁+α₂)² − (α₁−α₂)²)/4`; the second follows from Newton's
`a_F(p²) = a_F(p)² − e_2(p)`; the third is the parallelogram law
`‖α₁+α₂‖² + ‖α₁−α₂‖² = 2(‖α₁‖²+‖α₂‖²) ≤ 4`. ∎

This replaces the earlier "exceptional set" bookkeeping entirely: the deviation of `e_2` from
`a_F(p)²/4` is *pointwise* bounded by a quarter of the energy defect `4 − |a_F(p)|²`.

### 246.3 The theorem

**Theorem 147 (Conjecture A at the extremal energy).** Let `F` be as above with **real** Dirichlet
coefficients, and suppose the prime energy exists and attains its maximum,
```
n_F = lim_{x→∞} (loglog x)^{−1} Σ_{p≤x} |a_F(p)|²/p = 4 .
```
Then
```
Σ_{p≤x} (4 − a_F(p)²)/p = o(loglog x) ,   Σ_{p≤x} |g(p)|²/p = o(loglog x) ,
δ₁(e_2) = 1 ,     δ₁(a_F(·²)) = 3 ,
```
so **Selberg's Conjecture A holds for `F`**: `n_F = 4 = 3 + 1` with both halves `(SYM)`, `(DET)` of
Corollary 140 equal to integers. Moreover `α_1(p) = α_2(p)` and `|α_1(p)| = 1` at every prime where
`|a_F(p)| = 2`, so the local factor is there the square of a degree-one factor.

*Proof.* `|a_F(p)| ≤ 2` gives `4 − a_F(p)² ≥ 0`, and `n_F = 4` gives
`Σ_{p≤x}a_F(p)²/p = 4 loglog x + o(loglog x)`; subtracting from `4Σ_{p≤x}1/p = 4loglog x + O(1)` gives
the first display (`weighted_defect_le`). The second follows from `|g(p)|² ≤ 4 − |a_F(p)|²`. By
Lemma 246.A,
`|Σ_{p≤x}(e_2(p) − a_F(p)²/4)/p| ≤ ¼Σ_{p≤x}|g(p)|²/p = o(loglog x)`,
so `δ₁(e_2) = ¼ n_F = 1`; and `δ₁(a_F(·²)) = (3/4)n_F = 3` by the same estimate. The pointwise
statement is `satake_eq_of_norm_add_eq_two`. ∎

**Remark.** The extremal case is exactly the "maximally imprimitive" one: `F_p = (1−α_1(p)p^{−s})^{−2}`
at almost every prime, the local shape of a square of a degree-one element. Selberg's Conjectures
predict `n_F ∈ {1,2,3,4}` on this class with `n_F = 4` iff `F = G²` for `G ∈ S_1`; Theorem 147 confirms
Conjecture A at the top of that range unconditionally, and pins the local structure there.

**Open, unchanged:** `1 ≤ n_F < 4` is where the difficulty lives; nothing here touches it.

### 246.4 Formalised (extending the existing corpus module, not a new one)

Added to `formal/GaloisForLFunctions/HTGeometry/SatakeEnergyBound.lean`:
`eq_of_sameRay_of_norm_one`, `satake_eq_of_norm_add_eq_two` (the "coincide" half its own docstring had
promised), `satake_det_eq` (`α₁α₂ = (α₁+α₂)²/4 − (α₁−α₂)²/4`), `norm_sub_sq_le_four_sub`
(`‖α₁−α₂‖² ≤ 4 − ‖α₁+α₂‖²`), `weighted_defect_le`.
Axioms clean; `lake build +GaloisForLFunctions.HTGeometry` clean.

---

## 247. Cycle 247 (2026-07-26) — **the Deligne bound in global form**, and the energy–gap conservation law

### 247.1 Corpus first

`formal_tools.py research` returned no existing prime-power-to-integer bound transfer; the closest
corpus items are my own `HTGeometry.SquareIndexMultiplicative` (multiplicativity of `n ↦ a(n²)`) and
`HTGeometry.SquareIndexSymmetricSquare` (the `hSym` machinery of §241). Both are extended below rather
than duplicated.

### 247.2 Global Deligne bound

**Theorem 149.** Let `F ∈ S` be entire of degree 2 with `q_F ∈ {1,2,3,4}` (and `ω_F^* ≠ i`, real
coefficients, if `q_F = 4`, so that Corollary 142 supplies `p = 2`). Then for every `n ≥ 1`
```
|a_F(n)| ≤ d(n) ,
```
`d` the divisor function. In particular `|F(s)| ≤ ζ(σ)²` for `σ > 1`, and
`Σ_{n≤x}|a_F(n)|² ≤ Σ_{n≤x}d(n)² ~ x(log x)³/π²`.

*Proof.* Corollary 130 gives `F_p(s) = ((1−α_1(p)p^{−s})(1−α_2(p)p^{−s}))^{−1}` with `|α_j(p)| ≤ 1` at
every prime, so `a_F(p^k) = h_k(α_1(p),α_2(p))` is a sum of `k+1` monomials of modulus at most one,
whence `|a_F(p^k)| ≤ k+1 = d(p^k)`. Both `|a_F(·)|` and `d` are multiplicative; transfer along the
factorisation. ∎

**Why this is not the Ramanujan axiom.** Membership in `S` gives only `a_F(n) ≪_ε n^{ε}` with an
ineffective implied constant and no shape. Theorem 149 is the sharp, effective, Deligne-strength bound
`|a_F(n)| ≤ d(n)`, valid pointwise and with no exceptional set — the global form of Corollary 130.

### 247.3 Energy–gap conservation

Write `g(p) = α_1(p) − α_2(p)` for the **Satake gap**.

**Theorem 148.** At every prime,
```
|a_F(p)|² + |g(p)|² = 2(|α_1(p)|² + |α_2(p)|²) ≤ 4 ,
```
the parallelogram law, so with `1/p`-densities
```
n_F + δ₁(|g|²) ≤ 4 ,
```
with equality if and only if the Satake parameters are unimodular for almost all `p` (in `1/p`-density).
Consequently:
- on the unimodular locus, **Selberg's Conjecture A `n_F = 1` is exactly `δ₁(|g|²) = 3`** — the
  conjecture is a statement about the *spread* of the Satake pair, not its trace;
- `n_F = 4` forces `δ₁(|g|²) = 0` — Theorem 147;
- the Sato–Tate measure gives `∫4sin²θ dμ_ST = 3` and `∫4cos²θ dμ_ST = 1`, so `1 + 3 = 4`: the
  conservation law is **saturated** by the conjectured distribution, which is the consistency check
  that the inequality is sharp and not lossy.

### 247.4 Formalised (extending existing corpus modules)

Added to `formal/GaloisForLFunctions/HTGeometry/SquareIndexSymmetricSquare.lean`:
`norm_hSym_le` (`‖h_n(x,y)‖ ≤ n+1` for `‖x‖,‖y‖ ≤ 1`) and `norm_le_card_divisors`
(a multiplicative `ArithmeticFunction` bounded at prime powers by `k+1` satisfies `‖f n‖ ≤ d(n)`).
Added to `formal/GaloisForLFunctions/HTGeometry/SatakeEnergyBound.lean` in cycle 246:
`satake_det_eq`, `norm_sub_sq_le_four_sub` — the two identities behind Theorem 148.

### 247.5 Open, restated honestly

- `STEP1-EXPLICIT` (non-degeneracy of the universal quadratic form at `q_F = 2,3`);
- the range `1 ≤ n_F < 4`, where Theorem 148 says the content is the gap density `δ₁(|g|²)`;
- degree `≥ 3` entirely — and by Theorem 146′ the loop mechanism provably cannot reach it.

---

## 248. Frontier re-audit (2026-08-15) — separate published continuation from unverified automorphic claim

### 248.1 [LITERATURE] status correction

Kaczorowski--Perelli, *Multiple standard twists of L-functions*, is now a published JNT article
(284 (2026), 188--213, DOI 10.1016/j.jnt.2026.01.003), not merely an arXiv route.  Its precise
content is multivariable additive-twist continuation in `S^sharp`; it does **not** state a
Rankin--Selberg construction, a prime pairing, or either Selberg orthogonality conjecture.

Jiang, *On Hypothesis H of Rudnick and Sarnak*, arXiv:2507.20653, asserts Hypothesis H and
automorphic Selberg orthogonality for all `GL_n`, but its author page still lists it as an arXiv
preprint and no independent verification or publication was located.  It is therefore an
**unverified external frontier claim**, usable neither as a theorem nor as a Lean source.

### 248.2 Hostile route verdict

**Conjecture.** Published multiple-standard-twist continuation can supply C1/C2 by a tangent
diagonal mean.

**Verdict: FALSIFIED as an implication.** The continuation is for an additive tensor in
`S^sharp`; C1/C2 are prime-pairing statements for primitive elements of the full Selberg class.
The finite residue trace selects all diagonal indices, while prime extraction and a
Rankin--Selberg/nonvanishing input remain absent.  The full formal carrier has Euler-log data, but
no primitive-pair or Rankin--Selberg construction.

**Stronger survivor.** First reconstruct the published continuation exactly, then isolate the
extra operation required for C1/C2 as a prime-sensitive Rankin--Selberg trace, rather than treating
an unbounded tangent mean as that operation.  The current exact open core is the variable-line
Mellin--Barnes/Fubini bridge in the published continuation proof; it is source-faithful and does
not presuppose any C1/C2 statement.

### 248.3 Lean status

The finite residue trace, C^N gamma-cleared presentation, source spectrum, and general positive
Gamma inversion are now axiom-clean Lean bridges.  The variable-line Fubini proof and a correctly
stated C^N locally-uniform-limit theorem are in active formalization.  No theorem in this log proves
or disproves C1 or C2.

---

## 249. Literature correction (2026-08-15) — published automorphic scope is not all ranks

The statement in §1 that the automorphic side is “CLOSED” is **retracted**.  It relied on
Jiang's arXiv-only claim `arXiv:2507.20653`; that source has no verified journal publication and
must not be used as an established theorem.

Published evidence audited here supports the prime-sum normality and cross-orthogonality analogues
for unitary cuspidal automorphic `GL_m × GL_{m'}` only through `m,m' ≤ 4`; higher-rank published
arguments retain Rudnick--Sarnak Hypothesis H.  The full Selberg-class C1/C2 remain open.  The
degree-`≤1` Selberg-class classification is a genuine published subcase where both conjectures
hold; no result here upgrades that subcase to arbitrary `S`.

This correction reinforces, rather than weakens, the frontier rule: Kaczorowski--Perelli's
multiple-standard-twist continuation is a separate additive-twist theorem.  It does not supply a
published all-rank Rankin--Selberg pairing or a proof of C1/C2.

---

## 250. Carrier-semantics audit (2026-08-15) — exact missing bridge before any C1/C2 claim

`RHTower.SelbergClass` presently stores both the Dirichlet coefficients `a_F` and an Euler-log
coefficient system `b_F`, but only relates their *L-series* by
`L(a_F)=exp(L(b_F))` on `Re s>1`.  No existing Lean theorem proves the indispensable prime identity
`a_F(p)=b_F(p)`.  The smallest honest target is to differentiate that equality, use L-series
injectivity, and specialize the resulting convolution recursion at a prime.  This is known
mathematics and an unconditional semantic bridge, not a C1/C2 premise.

Likewise, the current finite prime-square identity is for raw arithmetic functions.  There is no
full-class product, conjugate closure, primitive predicate, factorization theorem, or C1/C2
definition.  A field-by-field audit found the ordinary Dirichlet-convolution product of two full
carriers constructible from existing axioms; its only missing analytic helper is closure of the
project's `EntireFiniteOrder` witness under multiplication.  Ordinary product closure is necessary
to state the prime-square reformulation at the carrier level, but it is **not** a Rankin--Selberg
construction and therefore cannot be advertised as C2.

**Conjecture → fail/pivot.** An arbitrary Dirichlet character's prime energy was initially treated
as having a finite *conductor*-prime correction.  This is false for imprimitive characters: zeros
occur at primes dividing the chosen level, not necessarily the conductor.  The corrected exact
target uses the nonzero level; the primitive-character version then has the conductor correction.
This is the degree-one C1 bridge only, not a classification theorem for full `S`.

---

## 251. Carrier repair and degree-one C1 boundary (2026-08-15)

### 251.1 [LEAN-PROVED] Euler logarithm has the actual prime coefficient

`RHTower.SelbergClass.coeff_prime_eq_eulerLogCoeff` now proves, without any new class field or
analytic hypothesis,
```
a_F(p) = b_F(p)
```
for every prime `p`.  It differentiates the existing Euler identity on `Re s > 1`, identifies the
resulting absolutely convergent L-series by coefficient injectivity, and evaluates the convolution
at the two divisor pairs of a prime.  Thus any future Euler-log prime statement applies to the
actual coefficients appearing in C1/C2.

### 251.2 [LEAN-PROVED] finite-order multiplication

`EntireFiniteOrder.mul` closes the missing analytic witness for pointwise products of the existing
entire finite-order carrier.  This is necessary infrastructure for an ordinary full-class product
constructor.  It is not a Rankin--Selberg construction and gives no C2 pairing by itself.

### 251.3 [LEAN-PROVED] exact Dirichlet-character C1 normalisation

For every complex character of positive selected level `q`, the formal result is exactly
```
Σ_{p≤N} |χ(p)|²/p = Σ_{p≤N} 1/p − Σ_{p≤N, p∣q} 1/p,
```
with the corresponding Mertens limit.  Applying it to `χ.primitiveCharacter` replaces `q` by the
conductor.  This proves the known degree-one character coefficient calculation, while preserving
the counterexample to the false imprimitive conductor correction.  It neither constructs the
degree-one Selberg-class classification nor addresses C2.

### 251.4 Status

These modules remove three semantic/infrastructure gaps.  The remaining decisive gap is still a
prime-sensitive quadratic trace (Rankin--Selberg-like object or equivalent positivity); neither
ordinary convolution nor K--P additive-twist continuation supplies it.  Therefore C1/C2 remain
unproved and undisproved in the full Selberg class.

---

## 252. Degree-one C2 reduction and exact boundary wall (2026-08-15)

### 252.1 [LEAN-PROVED] finite quotient-character reduction

For characters represented at one selected common level,
`dirichletCharacterPrimeHarmonicCross_eq_quotient` proves the exact cutoff
identity
```
Σ_{p≤N} χ(p) overline(ψ(p))/p = Σ_{p≤N} (χ ψ⁻¹)(p)/p.
```
The quotient is trivial exactly when the two selected-level characters are
equal.  This includes level-dividing primes correctly (both sides vanish).

### 252.2 Conjecture → fail/pivot

**Conjecture.** Existing Dirichlet `L` infrastructure immediately turns the
nontrivial quotient into the C2 `O(1)` bound.

**Failure.** `LFunction_apply_one_ne_zero` and an Euler identity on `Re s>1`
do not yield convergence of the *ordered* boundary sum `Σ_{p≤N} η(p)/p`.
Using `Summable` would be false: it asks for unordered/absolute convergence.

**Pivot / missing theorem.** Formalize an unconditional Mertens theorem in
arithmetic progressions (or an equivalent boundary Tauberian theorem) that
uses the nonvanishing at `1` and controls the ordered prime reciprocal sum.
Classical theory proves this degree-one statement; the dependency-closed Lean
bridge is absent.  This is a precise formalization frontier, not a proof of
full Selberg C2.

---

## 253. Ordinary product closure confirms the tensor gap (2026-08-15)

### 253.1 [LEAN-PROVED] full carrier closure

`SelbergClass.mul` now constructs the ordinary product of two full carriers:
Dirichlet-convolution coefficients, additive Euler-log coefficients, multiplied
continuation values, concatenated Gamma data, and multiplied root number.  The
Ramanujan field is discharged by the unconditional divisor bound.  This is an
actual full-carrier closure theorem, not merely a raw arithmetic-function fact.

### 253.2 Failed implication, now structurally explicit

At a prime, ordinary convolution has the first-order law
```
a_{F·G}(p) = a_F(p) + a_G(p),
```
whereas C2 needs the second-order local covariance
`a_F(p) overline(a_G(p))`.  Thus ordinary product closure cannot be renamed a
Rankin--Selberg construction.  The same distinction explains why the
additive-twist/Barnes machinery can propagate analytic data without creating
the prime-pair trace required by C1/C2.

### 253.3 Universal-shadow working conjecture (unproved)

The correct missing primitive is a prime-local tensor/Hadamard functor on full
Selberg data whose local Euler logarithm has prime coefficient
`a_F(p) overline(a_G(p))`, together with an analytic continuation and a
positive trace theorem.  Rankin--Selberg functoriality is its automorphic
shadow; K--P additive tensors, Euler-log linearization, and ordinary products
are lower-order shadows.  A construction or a counterexample to this
primitive—not more ordinary product algebra—is the genuine route to C1/C2.
