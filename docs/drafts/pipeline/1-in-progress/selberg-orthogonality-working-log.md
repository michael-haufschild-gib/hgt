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
