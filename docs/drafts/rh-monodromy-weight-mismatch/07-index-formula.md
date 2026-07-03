# 07 — M1 made precise: the transfer theorem and the isolated hypothesis (H_k)

Register: SEARCH-register document carrying one LEDGER-candidate theorem (§3) with a
complete paper proof. Companions: `06-reduction.md` (the Reduction, consumes (R_k)),
`00-approach.md` §5–§6 (mechanism M1, q62 transposition). Board item C3.

Outcome in one line: **M1 is now a theorem with one isolated hypothesis** — (H_k), a
conditional sup-norm recurrence of 1-dimensional boundary data at a single defect box —
and (H_k) ⟹ (R_k), so with the proven Reduction: (D) + (H_k ∀k) ⟹ RH.

---

## 1. The cocycle is a coboundary (structure of w_k)

Objects as in 06-reduction §1: clean σ₀ ∈ (1/2, 1), H > 0, admissible boxes
B(T) = [σ₀, 2] × [T, T+H], count n(B(T)) by the argument principle, w_k = n mod 2^k.

Anchor a continuous branch of arg ξ at s = 2 (ξ(2) ≠ 0, banked `xi_two_ne_zero`) and set
S_{σ₀}(t) := (1/π)·(arg ξ continued along 2 → 2+it → σ₀+it). Splitting ∂B(T) into its
four edges gives the structural identity

w_k(B(T)) = [ S_{σ₀}(T+H) − S_{σ₀}(T) ] + (right-edge + horizontal corrections) mod 2^k,

i.e. **the cocycle is the mod-2^k discrete derivative of an S(σ₀, ·)-type height
function**, up to corrections with named regularity: the right edge (Re s = 2) carries an
absolutely convergent Dirichlet series plus a smooth archimedean drift — Bohr-almost
periodic plus slowly varying — and the horizontal edges are the usual Backlund-type
sign-counting terms. (Exact orientation/branch bookkeeping is routine and deferred to the
Lean card A3; nothing below depends on the sign conventions.) `[PROVED HERE — soft,
bookkeeping deferred]`

Prime-side contact: at abscissa σ₀ > 1/2 the classical representations of S(σ₀, T)
against prime sums Σ Λ(n) n^{−σ₀} sin(T log n)/(π log n)-type truncations hold *in mean*
(Selberg-shape; exact statements to be sourced at promotion `[CHECK]`). Mean/moment
control is exactly what CANNOT see w_k — next section.

## 2. Why linear probes are parity-blind (the inventory, banked)

Three anchors already in the parent ledger (audit F1–F9; do not re-derive):
- **S(T)-CLT RH-blindness** — the Gaussian/moment statistics of S do not distinguish
  RH-true from RH-false configurations.
- **Projection blindness** — ambient Bohr-torus data cannot decide winding; any coarse
  mechanism must inject source data (this killed M2).
- **Faithful detection = quadratic/signature OR global winding/index** — the ledger's
  own classification of what CAN see the invariant.

Conclusion of the inventory: w_k = (coboundary of S mod 2^k) is an integer-valued,
topological functional; every linear/statistical channel to the primes (moments of S,
linear statistics Σφ(γ), limiting distributions) is structurally blind to it. The only
faithful channels are index/winding transfer or signature forms. M1 must therefore be
routed through a *transfer* mechanism, not through statistics. That is what §3 does.

## 3. The transfer theorem — M1 as a conditional theorem

**Lemma (Rouché transfer). [PROVED HERE]** Let T* be admissible with margin
m(T*) := min_{s ∈ ∂B(T*)} |ξ(s)| (positive: the boundary is compact and zero-free by
admissibility). Let τ ∈ ℝ satisfy

sup_{s ∈ ∂B(T*)} |ξ(s + iτ) − ξ(s)| < m(T*).

Then T* + τ is admissible and n(B(T* + τ)) = n(B(T*)); in particular
w_k(B(T* + τ)) = w_k(B(T*)) for every k.

*Proof.* Set g(s) := ξ(s + iτ), analytic on a neighbourhood of the closed box. On
∂B(T*): |g − ξ| < |ξ|, so g ≠ 0 there (|g| ≥ |ξ| − |g − ξ| > 0), which is admissibility
of T* + τ since ∂B(T*+τ) = ∂B(T*) + iτ; and Rouché's theorem gives ξ and g the same
number of zeros (with multiplicity) inside B(T*). The zeros of g in B(T*) are exactly
the zeros of ξ in B(T* + τ), shifted. ∎

**Hypothesis (H_k) — [OPEN CORE, isolated].** For every clean σ₀ > 1/2 and H > 0 with
D_{σ₀,H,k} ≠ ∅ there exists T* ∈ D_{σ₀,H,k} such that the *return set*

R(T*) := { τ ∈ ℝ : sup_{s ∈ ∂B(T*)} |ξ(s + iτ) − ξ(s)| < m(T*) }

has positive upper density. (R(T*) is open and contains τ = 0; the demand is that it is
not a sporadic set.)

**Theorem (M1, conditional). [PROVED HERE]** (H_k) ⟹ (R_k). Consequently, by the
Reduction (06-reduction §3): (D) + (H_k) ⟹ RHLadder k, and (D) + (H_k for every k) ⟹ RH.

*Proof.* If D_{σ₀,H,k} ≠ ∅, take T* from (H_k). By the Lemma, T* + R(T*) consists of
admissible heights whose windows carry the same nonzero w_k, so T* + R(T*) ⊆ D_{σ₀,H,k};
positive upper density of R(T*) transfers to D_{σ₀,H,k}. That is (R_k). ∎

**Symmetry slack (remark).** The Lemma never uses that g is a vertical shift of ξ — only
analyticity and the boundary bound. Since ξ is real on ℝ and satisfies ξ(s) = ξ(1−s),
the data may return *up to the dihedral symmetry* (conjugation-reflected returns transfer
defects between heights ±T; FE-reflected returns transfer to the mirror box) and the
transfer still runs. So mechanisms producing only symmetrized or partial returns still
suffice for (H_k). This slack — invisible to the full-count formulation — is what the
mod-2^k coarsening buys on the mechanism side: the defect *notion* is coarser (D smaller,
the conditional weaker), and a ℤ/2^k-invariant is a plausible target for symmetry
arguments where the full count is not.

**Why this does not reduce to Bagchi.** The engine (Rouché) is his — the C2-fetched
proof sketch uses exactly this transfer. The statement demanded is different in kind:
Bagchi's strong recurrence is an *unconditional* recurrence of the actual ζ-data on
2-dimensional compacts, and is *equivalent* to RH. (H_k) demands returns of
1-dimensional contour data only, at ONE point, with an *automatic positive margin* (the
contour avoids zeros by admissibility — approximation is never needed near a zero of the
target data, dodging the exact regime where universality is RH-hard), and only in the
counterfactual branch (RH true ⟹ D = ∅ ⟹ (H_k) vacuous). As with any complete
relocation, (H_k ∀k) sits at RH strength given the proven parts — the claim is not that
it is weaker in logical strength, but that it is a *different shape of statement*
(recurrence-rigidity of zero-avoiding boundary data) with different tools pointing at it
(Bohr–Jessen distribution theory at σ₀ > 1/2, FE/reality symmetrization, and the family
evidence: D–H defects recur with bounded gaps at sample scale, median 18).

**Attack-as-false (standing).** The suspect step is not the Lemma but the margin: near a
defect the interior holds zeros, and one may worry the boundary data is atypically small.
It is not *zero* (m(T*) > 0 always), but (H_k) fails if margins along the defect
subsequence decay faster than the return-frequency of the ambient a.p. structure can
match. This is quantitative and *measurable in the D–H family now* — see R6 below. A
measured failure there kills this route for ζ too (the mechanism would be dead in the
only world where defects exist); a measured success gives the first non-counterfactual
instance of the whole M1 chain.

## 4. The q62 transposition and the derivative companion `[CONJECTURE]`

q62's `index_formula_split` pattern: a global rational identity over fixed points plus
per-term pinning kills configurations. The ζ-side candidate pairing is the derivative:
Speiser's theorem (RH ⟺ ζ' zero-free in 0 < Re s < 1/2) and the Levinson–Montgomery
quantitative pairing (ζ and ζ' have essentially equally many zeros left of the line) —
both statements delegated for exact-form verification (C4, in flight) `[CHECK]`.

`[CONJECTURE — parked until C4 returns]` Define the companion cocycle w_k' from ξ' on
the same boxes. FE + reality + the Speiser/LM pairing constrain (w_k, w_k') jointly —
a defect of ξ right of the line forces companion structure for ξ' *left* of the line,
where the mirror data lives in the region the FE controls. If the pair admits an index
identity (the analogue of Σ 1/(1−λ) = 0), per-box pinning of one component would
propagate recurrence to the other. This is the wild half of C3; the sober half is §3.

## 5. What this opens

1. **R6 (new compute, the decisive cheap test):** for a certified D–H defect box T*
   (t ≈ 167 or 177, window 2), measure the return set directly: sample
   sup_{∂B(T*)} |f(s+iτ) − f(s)| over τ ∈ [0, 600] and report the frequency and gap
   structure of sub-margin returns, against the margin m(T*). Pre-register before
   running: returns exist with positive frequency at gap scale comparable to the
   measured defect-gap median ≈ 18–21; if return gaps grow or margins starve, (H)-shape
   fails in the family — early kill for M1.
2. **A3 scope update:** the Lean card now includes the Transfer Lemma — check the
   toolchain for a usable Rouché/homotopy-invariance statement before writing anything
   `[CHECK mathlib]`; the atlas Schur–Cohn winding bridge stays the argument-principle
   candidate (audit F5).
3. **B2 collision:** FE ∧ positivity ⟹ symmetrized returns (the §3 symmetry slack is
   exactly the target shape for Arc B's machinery).
4. **C4 return feeds §4:** exact Speiser/LM statements decide whether the companion
   cocycle is well-posed; and C4's density-proof reading pins where (D) consumes the
   Euler product — completing the division-of-labor picture of 06-reduction §4.
