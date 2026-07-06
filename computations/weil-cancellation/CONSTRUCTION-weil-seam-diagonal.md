# Construction — the Weil/explicit-formula quadratic form on `completedGN`, and the seam-diagonal self-intersection

**Register: SEARCH** (conjectures labelled; banked Lean cited by name). Companion to
`PREREGISTERED_PREDICTIONS.md` (the falsification test this note interprets).

## 0. What the falsification test decided

The test asked: is the arithmetic's "signature cancellation" — the delicate balance that keeps the
Weil form positive and the zeros on the line — reachable at **finite** truncation, or **infinitary**?

The multiplicative principle settles it before any scaling-up of numerics: a finite Euler product
`∏_{p≤P}(1−p^{-s})^{-1}` is **zero-free** (a finite product of nowhere-zero factors). There is no
off-line mass at any finite multiplicative truncation — nothing to cancel. Off-line zeros, and with
them RH and any signature defect, are **created only in the analytic continuation of the divergent
product past `Re s = 1`**. So signature cancellation is intrinsically infinitary.

That is not the end of the story but its correct *decomposition*: the Weil form has two halves, and
only one of them is infinitary.

## 1. The quadratic form

Write `Λ(s) = A(s) ζ(s)`, `A(s) = ½ s(s−1) π^{-s/2} Γ(s/2)` (the archimedean factor `archFactor`),
and `completedGN = A · gN` for the truncated carrier. For an even test function `g` with transform
`ĥ(r) = ∫ g(u) e^{iru} du`, the Weil explicit formula reads

    Σ_ρ ĥ(γ_ρ)  =  P∞(ĥ)  +  Arch(ĥ)  −  Prime(g),                                  (EF)

with `ρ = ½ + iγ_ρ` (`γ_ρ` real ⟺ ρ on the line) and

    Arch(ĥ)  = (1/2π) ∫ ĥ(r) · [ Re ψ(¼ + ir/2) − log π ] dr           (archimedean place)
    Prime(g) = 2 Σ_n Λ(n) n^{-1/2} g(log n)                            (finite places; Λ = von Mangoldt)
    P∞(ĥ)    = ĥ(i/2) + ĥ(−i/2)                                        (pole term / the (s−1) anchor)

Taking `g = f ⋆ f*` (self-convolution) makes `ĥ = |f̂|² ≥ 0` on ℝ, and (EF) becomes a **quadratic
form** in `f`:

    W(f)  =  ⟨ f , (P∞ + Arch − Prime) f ⟩  =  Σ_ρ |f̂(γ_ρ)|².                          (W)

**Weil–Bombieri.** `W(f) ≥ 0` for all `f`  ⟺  RH. The negative eigenvalues of `Arch − Prime` are
exactly the **off-line-zero mass**: an off-line zero `γ = γ₀ + iδ` makes `|f̂(γ)|²` a genuine complex
evaluation that can drag `W` below zero. This negative part is the **signature defect** — the
Hodge-index/Hermite reading of hyperbolicity, now at the level of the intersection form rather than a
single Hankel matrix (`§0` of `PREREGISTERED_PREDICTIONS.md`).

## 2. The seam-diagonal self-intersection

**Function-field template (where this is a theorem).** On `C × C`, `W` is the intersection form on
middle cohomology; `Arch` is the **self-intersection of the diagonal** `Δ·Δ` (the geometric/degree
term), `Prime` collects the **Frobenius-correspondence traces** at the finite places, and RH is the
**negative-definiteness of the form on the primitive part** — the Hodge index theorem. The archimedean
term is the diagonal's own self-pairing; the prime terms are its pairings against the finite
correspondences.

**Number-field seam.** The completion `Λ = A·ζ` is the weld that glues the archimedean place `∞`
(the `Γ`-factor `A`) to the finite places `p` (the Euler product in `ζ`). The **seam-diagonal
self-intersection** is `Arch` evaluated on a diagonal-localized test function — the `∞`-adic
self-pairing of the diagonal, a **regularized** (Hadamard / functional-equation-fixed) number, not
one propagated by any flow. The weight `½` inside `A` is its fixed point.

## 3. The split, and the verdict for #1

The two halves behave oppositely — but **not** as "positive anchor vs load." The arch density is
*indefinite*, and getting this right sharpens the verdict.

- **`Arch` (the seam-diagonal self-intersection): fixed, explicit, finite, present at every `N` — but
  sign-indefinite.** The density `windingRate(r) = ½[Re ψ(¼ + ir/2) − log π]` is **negative** at low
  frequency (`windingRate(0) = ½(Re ψ(¼) − log π) ≈ ½(−4.227 − 1.144) ≈ −2.7 < 0`) and turns positive
  only above a bounded height, growing like `½ log(r/2π)` thereafter (the **winding floor**). So `Arch`
  is a fixed explicit form with a negative core and a `log`-growing positive tail — *not* a positivity.
  It is present in `completedGN` for every truncation because the seam (`A`) is never truncated.

- **`Prime` (the finite-place accumulation): infinitary.** The off-line mass / negative eigenvalues
  appear only as the prime sum accumulates to `∞` — the divergent product continued. Each finite
  `Prime_X` is a finite-rank perturbation of the fixed `Arch`; none reproduces the RH-signature.

- **`P∞` (pole term / the `(s−1)` anchor): fixed.** The `ζ`-pole contribution, present at every `N`.

**Verdict.** The positivity `W = P∞ + Arch − Prime ⪰ 0` — which *is* the signature / the RH content —
is a property of the **whole** form, and it is genuinely **infinitary**: not even the arch half is
positive on its own, so there is no finite sub-constraint whose satisfaction is RH-relevant. What
finite `N` delivers is only the **explicit ingredients** — `Arch` (the winding form, banked exactly)
and `Prime_X` (the truncated von Mangoldt Gram form) — *not* any positivity. So `#1`'s
"signature with cancellation" is infinitary through and through; the finite carrier hands you the
form's pieces, never its positivity.

Stated as "constraint, not flow":

> the completed object is fixed by the **balance constraint** `P∞ + Arch − Prime ⪰ 0` — an equation
> the continued limit satisfies, not a form grown additively. The seam (`Arch`, the winding form) and
> the pole are the fixed explicit ingredients; the primes are the infinitary load; RH is the balance.
> No finite truncation *is* the balance; it only supplies its terms. `[CONJECTURE]`

This is the corrected decision the goal asked for: `#1` is **a genuinely infinitary object**, not a
finite-`N` construction target — the "signature cancellation" is the whole-form balance and cannot be
localized to any finite piece. The finite reachable content is the *explicit arch form*, an ingredient,
which is why the seam machinery below is worth banking even though it is not itself the constraint.

## 4. The payoff: `Arch` is the banked winding machinery

The archimedean density in `Arch` is, verbatim, the winding rate already formalized. From
`WindingFloor.lean`:

    windingRate u = ½ (Re ψ(¼ + i u/2)) − ½ log π = ½ [ Re ψ(¼ + i u/2) − log π ].

Hence

    Arch(ĥ)  =  (1/π) ∫ ĥ(r) · windingRate(r) dr,

and the banked **winding floor** `windingRate u ≥ ½(log(u/2π) − 4/u² − π/u)` (`windingRate_ge`)
controls the **high-frequency tail** of the arch density: it is negative at low `r` and grows like
`½ log(r/2π)` once past the height where the floor turns positive. The reality of `completedGN` on the
line (`completedGN_im_eq_zero_on_line`, banked) is what makes `W(f) = Σ_ρ |f̂(γ_ρ)|²` real. So the
seam-diagonal self-intersection — the arch *form itself* — is **not new machinery**: it is the
winding-rigidity / winding-floor instruments, re-read as the archimedean term of the Weil/Hodge
intersection form.

This re-reads the "frozen lane": the winding-floor work *is* the explicit archimedean term of the
Hodge form — an ingredient of `#1`, exactly and finitely, even though the form's *positivity* is the
infinitary balance and lives elsewhere.

## 5. Next generative moves

1. **Bank the explicit arch term.** State `Arch(ĥ) = (1/π) ∫ ĥ · windingRate` in Lean and carry its
   `log`-growing high-frequency tail from `windingRate_ge` — a machine-checked identity for the
   seam-diagonal self-intersection *as an explicit form* (not a positivity), the finite-`N` ingredient
   of `#1`. Its indefiniteness (negative core) is the point: it shows the positivity cannot be localized
   here.
2. **Name the load precisely.** Write the truncated prime Gram form `Prime_X(f) = 2 Σ_{n≤X} Λ(n)
   n^{-1/2} g(log n)` and pose the open comparison `Prime_X ⪯ Arch + P∞` as the infinitary core — the
   multiplicative/continuation content the falsification test isolated.
3. **Collide with the parity front.** The negative eigenvalues of `Arch − Prime` are the off-line-zero
   mass whose **mod-2 reduction** is the conservation/parity flux (`15-conservation-program`). The
   Weil form is the **index refinement** of that flux; the seam-crossing rigidity
   (`SeamCrossingRigidity.lean`) counts the same off-line events the negative eigenvalues weigh. The
   shared object to construct is the map (off-line-zero index) → (parity flux), a signature-to-parity
   reduction — which tells you exactly how much the parity front throws away.

## 6. Update — the signature-to-parity reduction is now formalized

Move `§5.3` is built: `RHTower/SignatureParity.lean` formalizes the reduction map from the integer
zero-index (the signature, = the Weil off-line index) to the mod-`n` deck class (the parity), and
measures the discard exactly.

- The map: `deckRed n k = exp(2πi·k/n)`, a homomorphism `(ℤ,+)→(ℂ,×)`; the banked box charge
  `deckClass_multi_zero` equals `deckRed n (Σ mᵢ)` (`box_charge_eq_deckRed`).
- The discard: kernel `nℤ`; `deckRed_emod` (retains only `k % n`); `parity_discards_full_line`
  (discards a free `ℤ`, the pair count); at `n = 2`, one bit retained, pair count discarded.
- Reflection ⟹ discarded: `even_sum_of_fpf_involution` (built) ⟹ `reflection_paired_deckRed_two_eq_one`
  and `reflection_fixed_deckRed_two_eq_one`.

The parity keeps `ZMod n` and throws away the entire reflection-symmetric part of the index — exactly
the mass the Weil signature counts. The residual the parity does see is the genuinely unpaired,
unramified order — where the RH content sits, and the object the next construction must reach.
