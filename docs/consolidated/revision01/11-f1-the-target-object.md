# 11 — The 𝔽₁ Object: the constraint-side geometric target

**What this is.** A consolidation of everything the parent research corpus has established about the
**field-with-one-element (`𝔽₁`) object** — the geometry that would realise `ζ`/`ξ` as the zeta of an
arithmetic object carrying a Frobenius and a weight/purity structure, so that RH falls out as a *residue*
of that structure rather than being attacked directly.

**Why it sits here.** big-picture §1′ (the logical form of a constraint-proof) and lenses 7–8 name exactly
this object: the **non-RH-equivalent constraint** — a weight/purity rigidity structure — from which the
divisor's location is forced ("cannot be otherwise"), never proved as a target. The `𝔽₁` object is the
geometric carrier of that constraint. This document records *what it is, what has been built, where the wall
is, what is retired, and the current SOTA* — so the forward work (lens 8) is not re-derivation.

> **One-line consensus of the whole corpus.** Every route — Connes–Consani, Deninger, Weil-étale, Borger
> Λ-ring, modular/Eisenstein — converges onto a *single* master object: an **infinite-dimensional `𝔽₁`-Jacobian
> / self-product `Spec ℤ ×_{𝔽₁} Spec ℤ`** carrying a polarization of Hodge signature `(1, ρ−1)`. **Positivity is
> "free"** (Rosati positivity holds for *any* real polarization); **the wall is INTEGRALITY** — supplying a
> `ℤ`-form / polarization-compatible complex structure `J` for the `ℚ`-independent periods `{log p}`. "No uniform
> integer `q`" is the whole obstruction.

---

## A. Why `𝔽₁` is forced — the primes-≠-`q`-powers theorem `[LIT, elementary]`

The closed points of any variety `X/𝔽_q` have residue fields `𝔽_{q^{deg x}}`, hence norms `Nx = q^{deg x}` — a
*single geometric progression* `{q, q², q³, …}`. So `Z_X(s) = ∏_x (1 − q^{−s·deg x})^{−1}` is supported on `{q^k}`.
But the Riemann Euler product `∏_p (1 − p^{−s})^{−1}` is supported on `{2,3,5,7,…} ⊄ {q^k}`. **Therefore no variety
over any fixed field — of any dimension, abelian or Shimura — has `ζ`'s Euler factors.** The obstruction is the
**point-set**, *before* any positivity question.

The only escape: leave the category of schemes-over-a-field. As `q → 1` the quantization `q^{deg}` degenerates
(`1^k = 1`) and "degree" must be replaced by a **`log`-valued size** — this *is* the `𝔽₁` regime. A curve-tower
attack lands on `𝔽₁` by the point-set alone. This unifies the multiplicativity separator (only the Euler product,
not the functional equation, pins zeros — Davenport–Heilbronn & Epstein `ζ_Q` (`h>1`) have FE but off-line zeros)
with the class-number fact `Pic⁰(\overline{Spec ℤ}) = 0` as one statement: *the primes are not the closed points of
any positive (Deligne-type) geometry.*

---

## B. What the `𝔽₁` object is — the candidate realisations

### B1. The finite `𝔽₁` curve `Γ_S` `[constructed, toy]`
For a finite prime set `S` (`|S| = g`): `Γ_S` = **disjoint union of `g` circles `C_i` of circumference
`ℓ_i = log p_i`** (must be disjoint, not wedged — wedging manufactures spurious geodesics `log(p_ip_j)` and destroys
the Euler product). Ruelle zeta `Z_{Γ_S}(s) = ∏_i (1 − e^{−s·log p_i})^{−1} = ∏_{p∈S}(1 − p^{−s})^{−1}` (exact
truncated Euler product). Its **Jacobian is a *real* torus** `Jac(Γ_S) = ℝ^g/ℤ^g`, principally polarized by the
length form `Q = diag(log p_1,…,log p_g)` — **not an abelian variety: it has no complex structure.** *This absent
complex structure is the seed of every later obstruction.* Tropical Lefschetz on `Γ_S` reproduces the explicit
formula: `Σ_τ (Δ·Γ_τ) e^{−sτ} = Σ_n Λ(n) n^{−s} = −Z'/Z`; polarization volume `det Q = ∏ log p ↔` the `s=1` pole.

### B2. `Spec ℤ` as an infinite-genus curve over `𝔽₁` — the genus tension `[the central paradox]`
Connes–Consani frame the object by a verbatim tension: *the classical Jacobian of `Spec ℤ` (its ideal class group)
is trivial, suggesting **genus 0**; the spectral realization of the zeros suggests `Spec ℤ` is a curve of **infinite
genus**.* Categorically, `Pic⁰(\overline{Spec ℤ}) = 0` (class number 1, one archimedean place) ⟹ scheme-genus 0; the
infinite-genus Jacobian `ℝ^∞/ℤ^∞, diag(log p)` lives only in the **tropical/analytic/topos** category, not as a
scheme. The two pictures must be reconciled by the missing geometry.

### B3. The Connes–Consani arithmetic & scaling sites `[built — a topos, NOT a scheme]`
The **arithmetic site** = the tropical semiring as a structure sheaf on the topos `\widehat{ℕ^×}` dual to the
multiplicative monoid `ℕ^×`; the **scaling site** is its `ℝ₊ˣ`-extension. Primes appear as points and the scaling
flow is a Frobenius. **Crucially it is a *site/topos*, not a scheme with intersection theory** — so Faltings–Hriljac
(arithmetic Hodge index), which needs an actual arithmetic surface *over a base*, does not apply: the `𝔽₁`
self-product has **no base below `ℤ`**.

### B4. Borger Λ-ring / Witt vectors — the full-rank prime skeleton `[the arithmetic half, built]`
A **Λ-ring structure** on `ℤ` (big Witt vectors) is precisely an **`𝔽₁`-descent datum** (Borger), and it supplies a
**Frobenius lift `ψ_p` for *each* prime**, `ψ_p(x) ≡ x^p (mod p)` — *one independent direction per prime*, exactly
the escape from a single `q`. The Λ-ring self-product `ℤ ⊗_{𝔽₁} ℤ` (Witt construction) is a **full-rank,
prime-indexed intersection skeleton** that evades the `q`-power lattice. **But the Λ-ring is algebraic/categorical:
no Kähler metric, no Hodge index, no positivity.** (Caution: `ℤ` is the *initial* Λ-ring, so the *naïve* self-product
`ℤ ⊗_{𝔽₁} ℤ = ℤ` collapses to 0-dimensional — the object must be q-deformed / CM-enriched before a complex structure
can live on it.)

### B5. The Connes adele-class spectral triple — Frobenius = modular flow `[SOTA operator realization]`
The surface `M = L^∞(X) ⋊ C_ℚ`, `X = 𝔸_ℚ/ℚˣ` (adele class space), `C_ℚ = 𝔸_ℚˣ/ℚˣ` (idele classes) acting by scaling.
Tomita–Takesaki modular data: **modular operator `Δ = |·|`** (idele module), **modular flow `σ_t =` scaling by `e^t` =
the abstract Frobenius / "time evolution" for `Spec ℤ`**, **Dirac `D = log Δ = log|·|`** = generator of the scaling
flow. The geometric side of Connes' trace formula has periodic orbits of length `{log p}`. `M` is **type III₁** (the
archimedean place makes the module range all of `ℝ₊ˣ`). The zeros are localized on the **Sonine/Sonin cokernel
`H₀ = coker(E)`**: `spec(D|H₀) = {ρ}` — the zeros as an *absorption spectrum*. The explicit formula is a
**Lefschetz–Atiyah–Bott formula** `Δ·Γ_f = Σ_{fixed pts}(local index) = Σ_ρ f̂(ρ−½)` whose **fixed points are the
primes**.

### B6. Deninger's foliated dynamical system `[conjectural cohomology]`
The Weil explicit formula should be a **Lefschetz trace formula for a real flow `φ_t = exp(tΘ)`** on an
infinite-dimensional foliated `H^*_dyn(Spec ℤ)`; zeros = spectrum of the generator `Θ`. Regularized-determinant
identity: `ζ_X(s) = ∏_i det_∞((s − Θ_i)/2π | H^i_dyn)^{(−1)^{i+1}}`, so in degree one the nontrivial zeros are
exactly `spec(Θ_1)`. The **suspension/mapping-torus** `Σ = (ℝ_x × ℝ_t)/((x,t) ∼ (φ(x), t−1))` is a 2-D foliated
space with Weyl law `N(λ) ~ c·λ` (a *power* law — fixing the missing dimension), closed orbits = primes (length
`log p`), fixed point at `∞`. "The cohomology has not been constructed; the program organizes which structures one
is missing."

**These six are facets of one object.** Borger's Witt/Λ-Frobenius suspended = Deninger's foliated space; the Connes
adele-class triple is its operator realization; `Γ_S` is its finite truncation; the arithmetic site is its topos
shadow.

---

## C. The constructions — turning the frame into a Frobenius/Hodge object

### C1. The integer Frobenius tower and the `(α−1)/log q → ρ` rescaling `[the durable bridge]`
A tower `(L_g, Q_g) → ξ`: `H¹(C)` a rank-`2g` integral lattice with symplectic unimodular `J`, integer Frobenius
`F_g`, `char poly ∈ ℤ[T]`, functional equation `T^{2g} P_g(q/T) = q^g P_g(T)`. The `q→1` rescaling: `q = e^ε`,
`α_i = √q · e^{iθ_i}`, `θ_i = γ_i ε` ⟹ `α_i = e^{ε(½ + iγ_i)} = e^{ερ_i}`, so `(α_i − 1)/ε → ρ_i` and
`(1/ε) log F_g → diag(ρ_i)`. The **Weil circle `|α| = √q` becomes `Re ρ_i = ½`**. This `(α−1)/log q → ρ` map is the
corpus's durable contribution. *Caveat (hawking):* at `q→1` there is no curve (the `{log p}` are not `q`-powers), so
the tower must be built **abstractly** — "that existence is the entire remaining wall."

### C2. The `A + iB` split — `RH ⟺ A = ½` `[built, operator-identity form]`
Write `D = A + iB`, `A = (D+D*)/2`, `B = (D−D*)/2i`; `A` carries real parts `β`, `B` carries heights `γ`. With
`Φ = e^D` (Frobenius), `Φ*Φ = q = e` and monodromy `F = Φ^{−1}` (eigenvalues `e^{−ρ}`):
**`RH ⟺ F/√e unitary ⟺ F*F = e^{−1}·I ⟺ D + D* = I (A = ½)`.** BCH expansion: `2A = I + i[A,B] + (higher)`, so the
*entire* deviation from RH is carried by the commutator `[A,B] = (1/2i)[D*,D]`. **Corrected landing:** a self-adjoint
extension has real spectrum *automatically* (reality is free); the RH content is **completeness/exactness** — does
the real spectrum *exhaust* all zeros? In the squared variable `u_ρ = ρ(1−ρ)`, an off-line zero gives `Im u_ρ ≠ 0`,
which is *not* an eigenvalue of any self-adjoint extension, so an off-line zero is simply **MISSING**. The deficiency
`[A,B] ∝ [E,F]` (the prolate/Slepian time–frequency commutator) is **archimedean-only** — over `ℚ_p` the cutoffs
commute (`[E_p,F_p]=0`). *This is the same archimedean-vs-finite split as our prolate `4N+1` channel finding.*

### C3. The polarization / complex structure `J` `[the named missing object]`
The object needs a **polarization-compatible complex structure `J`** (`J² = −1`, `Q(J·,J·) = Q`) on the infinite
real `𝔽₁`-Jacobian, supplied **both integrally** (the margin survives) **and arithmetically** (Frobenius eigenvalues
= the zeros). Candidate: glue local CM-rotations `J_p` (multiplication by `i ∈ ℤ[i]` / a primitive 4th root in a
CM-by-`ℤ[ζ]` module — Weil numbers `|π|² = q ⟺` on the line) into one global integral `J`. Polarization-compatible
`J` form a **period domain `D = G(ℝ)/K`** (Siegel/Hermitian); the arithmetic `J` is a **special (CM) point**, and
specialness is a property of the **Euler-product map `{ψ_p}`** (Hecke correspondences / Borger Λ / Connes–Consani),
*not* of the generic source `{log p}`: **RH ⟺ the archimedean period point is simultaneously fixed (Hecke-stable)
under all commuting `{ψ_p}`.** Candidate concrete polarization `L = λ^{½}` (the archimedean `√(scaling)` / Γ-factor
+ pole-at-`s=1` "+1" ample class): `\widehat{NS} = ⟨L⟩ ⊕ L^⊥`, signature `(1, ρ−1)` with `L² > 0` (= Connes
semilocal positivity) and `D²_{prim} ≤ 0` (Hodge index); Weil sign `Q_W(f) = −D_f² ≥ 0` = RH. **`[NO-GO]` Building
`J` from the zero set is RH-equivalent** (Deninger zero-space lemma; Hard Lefschetz on zero-cohomology computes to
`(2β−1)b`) — `J` must be built from *arithmetic* data with zeros *emergent*, and must **fail for Davenport–Heilbronn
/ Epstein fakes** (hence must use the single Euler product).

### C4. Three names, one axis `[unification]`
The needed transverse-to-scaling axis is one object under three names: **(Borger)** big Witt vectors / Λ-ring with
Frobenius lifts `ψ_p`; **(Deninger)** foliated suspension, closed orbits = primes; **(de Bruijn–Newman)** heat-flow
`H_t` deformation of `ξ`, `Λ_{dBN}` = landing time. **Crux correction:** take the *invertible* Frobenius monodromy
`φ*` on leafwise `H¹` (a symmetry that constrains all cohomology at once), **NOT** the dissipative dBN heat flow
(parabolic, "cannot constrain its own initial data" — proves zeros real for `t ≥ Λ` but `Λ ≤ 0` is unreachable;
Polymath15 stalled at `Λ ≤ 0.2`). The heat flow is the modulus-semigroup `|φ*|^t`; the backward half (the phase) is
supplied by invertibility. Algebraically: Witt `F_p` completed by Verschiebung `V_p`, `F_pV_p = [p]`,
`V_pF_p ≠ F_pV_p` ⟹ noncommutative = **Bost–Connes** (`ℚ/ℤ ⋊ ℕ^×`).

---

## D. The crux — integrality, not positivity (the unifying thesis)

Every batch independently reached the same diagnosis. **"Positivity was never the wall; integrality was."**

- **D1 — positivity is free.** Rosati positivity holds for *any* real polarization (one-line theorem). Over `𝔽_q`
  the Néron–Severi form is an **integer lattice** with margin `≥ 1` (weight gaps `~√q`); Deligne's RH has an integer
  protecting the sign.
- **D2 — no-margin.** Over `𝔽₁` the periods are `log p` (transcendental, `ℚ`-independent by Baker, ratios
  accumulate), so the same positive form has **no floor**: `margin(X) = log2/log p_g ∼ log2/log X → 0` (certified to
  `X = 10⁷`). There is **no integer Néron–Severi lattice with uniform margin** — "no uniform integer `q`."
- **D3 — the von Neumann type.** `Spec ℤ` is **type-II₁/III** (real-valued dimensions, no spectral gap at 0), while
  `C×C` is **type-I** (integer Betti number, a protected margin). A real-valued index has **no gap at 0** — three
  languages (no integral margin / `log p` transcendental / `λ_min(Q_W) → 0` continuously) for *one* fact, and *that
  is why `Λ_dBN = 0` exactly.* The `q→1` limit dissolves the weight gap `√q > 1`.
- **D4 — mixed-Tate: no purity.** `ζ` is **mixed Tate** (weights 0 and 2), so Deligne purity (which needs a *pure*
  weight) does not apply — **`ζ`-RH = "purity for a mixed-Tate motive."** In motivic coordinates the irreducible core
  is **Brown 2012**: the motivic Galois group of `MTM(ℤ)` is **free pro-unipotent** (`σ_3, σ_5, …`, no relations) =
  a "motivic Baker" / no-relations wall. Classical Hodge theory polarizes pure/graded pieces, not the mixed
  extension; **CKS-for-free was retracted** — polarizability of the mixed (Eisenstein) variation *is* the wall, not
  a CKS output.
- **D5 — Deninger's polarization axiom = the whole problem.** A positive Hermitian `h` on `H¹_dyn` making the
  **normalized flow `U(t) = e^{−t/2} φ_1(t)` unitary** ⟹ `Θ_1 − ½` skew-adjoint (Stone) ⟹ `spec(Θ_1) ⊂ ½ + iℝ` ⟹
  RH. The deduction is short; **constructing the polarized carrier with positivity is the entire content**, and it is
  RH-strength. **Per-place purity fails:** the finite-prime local kernel `K_p(ψ) = 2r(cos ψ − r)/(1 − 2r cos ψ + r²)`
  goes negative (`K_p(π/2) < 0`); it is the positive Poisson kernel with the `m=0` diagonal removed, so the missing
  diagonal (the archimedean/pole term) must supply purity *globally* — no per-place purity exists.

---

## E. The recent SOTA — Connes–Consani(–Moscovici), 2006–2026 `[the live frontier]`

The `𝔽₁` program is *active SOTA*, not a closed chapter. Pieces actually built (none claims RH; the authors do not
claim it):

- **Weil positivity / archimedean** (`2006.13771`): the single archimedean place; "Weil positivity ⟹ RH"
  (RH-equivalent), a "potential conceptual reason."
- **Riemann–Roch for `Spec ℤ`** (`2205.01391`, `2306.00456`): RR treating `ℤ = 𝕊[X]` over the sphere spectrum / `𝔽₁`
  — Euler-characteristic, **not** a signature/Hodge-index theorem.
- **Semilocal positivity** (`2602.04022`, Connes 2026): on `Y_S = (∏_v Q_v)/Γ`, the compressed Weil form's positivity
  as `S →` all primes **⟺ RH**. The **archimedean half is proven** (Sonin/prolate-compressed positivity, no finite
  primes, small window `supp ⊂ (−log2, log2)`); the **finite/prime half (semilocal `S → ∞`) is the open content.**
- **Jacobian of `Spec ℤ`** (`2602.15941`) and **Absolute Geometry of `Spec ℤ`** (`2606.06604`): an absolute `𝔽₁`
  arithmetic curve; **Frobenius corresponds to multiplication by `p`** at both archimedean and `p`-adic local
  `ℂ`-points. *Outlook explicitly leaves the behavior of Frobenius eigenspaces under descent to periodic orbits as
  future work* — so the cohomology/purity/cofinality step is **not** proved there.
- **Zeta Spectral Triples** (CCM, `2511.22755`): self-adjoint operators using primes `p ≤ λ²`; a regularized
  determinant `det_reg` expected to converge to `ξ` — the convergence/selector is the open RH-strength gap.
- **Twisted Selberg determinant** (`2512.16681`).

**`[VERIFIED, literature]`** — the decisive caveat: **no full-rank `(1, ρ−1)` Hodge-index theorem on a `ζ`-attached
pairing exists.** The proven arithmetic Hodge-index theorems (Faltings, Hriljac, Moriwaki, Yuan–Zhang) hold on
genuine arithmetic surfaces / adelic line bundles and are **never `ζ`-attached**. The Connes–Consani Jacobian is a
monoidal/idempotent-semilattice object lacking the projective/adelic space, ample cone, and intersection/height
pairing those theorems require — "not a minor citation gap; the missing mathematical construction." Connes' own
candor (`1509.05576`): the spectral side "only sees the zeros on the critical line" *by construction* (an artificial
weight `ρ(x)`), so it **cannot exclude** off-line zeros; the sites are "only the semiclassical shadows of a more
mysterious structure underlying the compactification of `Spec ℤ`."

---

## F. The no-gos / retired branches — do not re-walk `[established eliminations]`

- **Finite carrier no-go** `[Lean-verified, FiniteCarrierNoGo.lean, 0 sorry]`: no finite-dimensional real `(V, F)`
  has complexified eigenvalues = `ξ`'s zeros, because `N(T) → ∞` (Riemann–von Mangoldt) while `χ_F` has finite
  degree. Signature/Rosati/Hodge structures cannot rescue — they do not change the *cardinality* of the spectrum. A
  finite Lefschetz package models only a finite truncation or a function-field rational zeta factor; **the `ξ`
  divisor is infinite**, so the carrier must be infinite-dimensional (Deninger/Connes), with the right targets being
  a finite truncation + limiting theorem, an inverse/direct limit of finite carriers, or the infinite-dim regularized
  determinant.
- **Resolution wall** `[proved-note, consumer half Lean]`: no bounded-type / bounded-prime / finite-degree
  certificate can prove RH — it is "structurally blind to every off-line zero at distance `δ ≲ 1/X`" (off-line signal
  `Δ_off ~ (Xδ)² ‖h‖` by Bernstein; needs `X ≳ 1/δ`). Adaptivity just reproduces "use all primes/all scales" = RH.
  Survivors: full Weil positivity (circular) or spectral/cohomological inheritance (Connes).
- **Schatten no-go** `[proved]`: raw prime modes `K_s e_p = p^{−s} e_p ∈ S_q ⟺ Re(s) > 1/q`; no fixed Fredholm
  determinant `det_q(I − K_s)` extends entire; archimedean Γ-factors don't change singular values; finite-rank repair
  cannot move the threshold (`S_q` is an ideal). Survivors require infinite-rank cancellation (relative/zeta/nuclear
  determinant-line).
- **`κ₋` = flow-of-weights atom count** `[KILLED]`: the adele-class factor is *unconditionally* type-III₁, so its
  flow of weights is ergodic/atomless regardless of RH ⟹ this `κ₋ = 0` unconditionally = **RH-blind**. Lesson: the
  faithful integer cannot be measure-theoretic; it must be spectral/intersection-theoretic. (This *elevated* the
  intersection-form route P4: inertia of the pairing on `HC²` of the NC arithmetic surface = signature `(1, ρ−1)`.)
- **GL₂ Connes–Marcolli off-diagonal** `[negative/localized]`: the cuspidal interior carries an off-diagonal cocycle,
  but it degenerates to GL₁/Bost–Connes diagonal **zero-blindness** on `ζ`'s Eisenstein/rank-1 boundary.
- **Bare-`J` / Brauer gluing** `[DEAD]`: unpolarized/un-integral complex structures glue too freely (the obstruction
  is the *polarized, integral* `J`, not a bare one).
- **Lee–Yang / ferromagnetic / positive-residue mechanism** `[FALSIFIED for ζ]`: `Q_W` is `~31%` frustrated, residues
  mixed-sign; replaced by Hermite–Biehler interlacing (real-rootedness with mixed residues).
- **Free infinite divisibility (FID)** `[KILLED numerically]`: the `ξ`-zero measure is not freely infinitely
  divisible (free cumulants alternate `κ₂>0, κ₄<0, …`); the zeros behave as a free Haar unitary on the circle, not a
  real-line FID law. (FID ⊋ RH anyway — sufficient, not equivalent.)
- **Modular-surface / Eisenstein-scattering branch** `[free half only]`: `φ(s) = ξ(2s−1)/ξ(2s)` makes the zeros
  Eisenstein scattering resonances, but they are **continuous** (non-cuspidal) spectrum ⟹ no Hodge/Rosati positivity;
  `φ` is **FE-data only** (holds on *and* off RH). The modular surface hands over the free FE/Krein half and **zero**
  RH content; per-prime residue `Res M_p = (1−1/p)/(2 log p) > 0` is sign-definite, divergent, zero-blind.

---

## G. Connection to the hgt program — `𝔽₁` as the §1′ constraint

**This is the object lenses 7–8 and §1′ point at.** The corpus's verdict makes the lens-8 picture concrete and
sharpens it:

- **The `𝔽₁` object is the constraint, not a mirror — but the corpus shows it converges back onto an RH-equivalence
  at its last step** (Connes semilocal positivity `⟺` RH; Hard Lefschetz on zero-cohomology `= (2β−1)b`; building `J`
  from zeros is circular). So `𝔽₁` is the *right place to stand* (non-`q`-power point-set, infinite-genus, a genuine
  weight structure to build) but the naïve completion re-enters the mirror hall. **The genuinely non-mirror sub-piece
  the corpus isolates is one abstract theorem:** a **type-II₁ symmetry-rigidity theorem** (the "T4" gap) forcing a
  *real-valued* index `κ₋` to **exactly 0** from self-duality alone — *no margin, no integer to estimate.* Templates
  (Avila reducibility, Lück `L²`-determinant, `ρ`-invariant vanishing) all exist but are currently blocked. This is
  the one ingredient that is *not* "assemble positivity from the zeros," hence the only lens-8-admissible target.
- **The Wheeler–DeWitt / superspace reading (the founding metaphor, now concrete).** The Connes adele-class triple
  realizes exactly "a constraint with no external clock": the **modular flow `σ_t` is the would-be clock** — but it is
  *canonical* (Tomita–Takesaki, state-independent up to inner), so there is no external time; **the state is the
  constraint's own cokernel** — the zeros live on the **Sonin cokernel `H₀ = coker(E)`**, i.e. as the kernel/cokernel
  of the band-limiting constraint `E`, not as a trajectory. `ĤΨ = 0` (WDW) ↔ "the divisor is the cokernel of the
  archimedean cutoff." The `q→1` dissolution of the integer margin is precisely "the clock degenerates": the weight
  grading that *would* tick (`√q > 1`) collapses, and what remains is a pure constraint with `Re ρ = ½` as its only
  consistent pointer state. **This is the superspace-and-clocks intuition realized as the type-III₁ modular geometry
  of `Spec ℤ`.**
- **Our revision01 apparatus is the finite-section shadow of this master object.** Direct identifications:
  our **`κ₋`** (faithful integer index) = the corpus's faithful integer / intersection-signature `(1, ρ−1)`; our
  **archimedean prolate `4N+1` channels proven faithful, semilocal/full open** (comp82) = Connes' **archimedean Sonin
  positivity proven, semilocal `S → ∞` open**; our **`s_d → 0` height-limit** = the corpus's **`margin = log2/log X →
  0` no-margin**; our **boundary-`Γ`-atom rank-one weld** = the archimedean `L = λ^{½}` ample class. The seam object
  `𝓜⁺` (where `∂_s` and `{σ_p}` coexist) is the hgt-native name for the `𝔽₁` self-product `Spec ℤ ×_{𝔽₁} Spec ℤ`.

**Forward (lens 8, the non-mirror move).** Do *not* re-attack the semilocal positivity (a mirror). Build the
**type-II₁ rigidity** on the named full-rank skeleton (Borger Λ-ring) with the named metric (archimedean Arakelov
Green's energy) — the open question being whether **self-duality alone forces the real-valued index to 0** without
estimating a margin. That is a constraint about the *object's symmetry*, not about its zeros, and RH would be its
residue. The hypertranscendence home supplies the provable ground to stand on; the `𝔽₁` weight structure supplies the
geometry; the rigidity theorem is the missing, genuinely-new piece.

---

## H. Citations (as named across the corpus)

**Field with one element / absolute geometry.** Connes–Consani: arithmetic site & scaling site (`1405.4527`,
`1603.03191`), Weil positivity/archimedean (`2006.13771`), Riemann–Roch for `Spec ℤ` (`2205.01391`, `2306.00456`),
semilocal positivity (`2602.04022`), Jacobian of `Spec ℤ` (`2602.15941`), Absolute Geometry of `Spec ℤ`
(`2606.06604`); Connes–Consani–Moscovici, Zeta Spectral Triples (`2511.22755`); Connes essay (`1509.05576`),
twisted Selberg determinant (`2512.16681`). Borger (Λ-rings / big de Rham–Witt / `𝔽₁`-descent); Deitmar (monoid
schemes); Toën–Vaquié; Lorscheid (blueprints); Durov (`0704.2030`, generalized rings `𝔽₁, ℤ_∞`); Soulé; Segal
Γ-rings / TC as "absolute algebra."
**Cohomology / dynamics.** Deninger (ICM 1998, `math/0204110`, foliated dynamical system); Flach–Morin (Weil-étale);
Milne (`1509.00797`). Pollicott–Ruelle / Dyatlov–Zworski / Dang–Rivière (resonances). de Bruijn–Newman /
Rodgers–Tao (`1801.05914`) / Polymath15 (`Λ_{dBN} ≥ 0`).
**Operator / NCG.** Connes (trace formula, adele-class spectral realization, Sonin cokernel); Connes–Moscovici
(residue cocycle / local index; 2021 prolate); Bost–Connes (`ℚ/ℤ ⋊ ℕ^×`, KMS, type-III₁); Connes–Marcolli (GL₂);
Tomita–Takesaki, Connes–Takesaki (flow of weights), Connes–Haagerup (III₁ uniqueness); Slepian (prolate `EFE`);
Berry–Keating (`xp`).
**Hodge / arithmetic intersection.** Weil (correspondence ring, `C×C`); Deligne (Weil II, weight gaps `~√q`); Mumford
(Rosati positivity); Faltings (1984) / Hriljac (1985) / Moriwaki / Yuan–Zhang (`1304.3538`) (arithmetic Hodge index);
Bismut–Gillet–Soulé (Quillen metric); Amini–Piquerez & Adiprasito–Huh–Katz & Babaee–Huh (tropical/matroid
Hodge–Riemann); Mikhalkin–Zharkov, Allermann–Rau (tropical Jacobian/intersection); Bass–Ihara, Hashimoto
(non-backtracking).
**Motivic / transcendence.** Deligne–Goncharov & Brown 2012 (`MTM(ℤ)`, free pro-unipotent Galois group, `ζ(odd)`);
Baker–Wüstholz (`{log p}` independence). Cattani–Kaplan–Schmid (LMHS polarization — *applies only after*
polarizability); Griffiths/Schmid (polarized VHS curvature); Beilinson–Bloch (regulators); Kronecker limit formula /
Dedekind `η`.
**Modular / scattering / canonical systems.** Selberg/Iwaniec & Lax–Phillips & Faddeev–Pavlov (`φ(s) = ξ(2s−1)/ξ(2s)`);
Arthur (truncation); Burnol / Suzuki (`1204.1827`, canonical system); de Branges / Krein–Langer (Pontryagin index,
HB innerness); GORZ/DLMW (uniform Jensen-hyperbolicity); Manin (real multiplication / NC torus θ-Jacobian);
Voiculescu / Speicher (free probability). Iwasawa / Mazur–Wiles (Main Conjecture — a theorem, structural analogy
only, no transfer to RH).

---

*Status of this object: **not proven, not falsified.** It is the convergent target of the entire spectral/geometric
program — the place where "constraint, not flow" becomes a concrete construction problem. The next move (lens 8) is
the type-II₁ rigidity theorem, built on the Borger skeleton with the Arakelov metric — not another restatement of the
positivity that is RH.*
