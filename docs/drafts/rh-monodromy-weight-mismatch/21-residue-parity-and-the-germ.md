# 21 — Residue Parity: the (SMOOTH) No-Go and the Arithmetic Germ

**Register: SEARCH.** Task #133. The question: can the explicit formula read the
residue parity of ξ′/ξ off the line (⟺ ε(Ξ₁) = 0 ⟺ (WR_1), doc 19 §3)?

## 1. The free level and the paid level

Unconditionally, (ID) mod 2 is an exact boundary identity: the monodromy sign of √ξ
around ∂W (the level-2 deck class, banked) equals sign(Ξ(t₋)Ξ(t₊)) at the two slit
endpoints — because for the REAL carrier a non-real conjugate zero pair contributes
|t − τ|² > 0 at real points: complex pairs are invisible to real sign data. That
positivity mechanism is the ONLY known sign-extraction, and it reads L mod 2 only.
The paid level — mod 4, i.e. N mod 2 — is exactly the rung.

## 2. The (SMOOTH) no-go shape

Explicit-formula pairings h ↦ Σ_ρ h(ρ) are ℂ-linear in h and vary smoothly with any
parameter of h; ε is 2-torsion. Extracting torsion from a linear pairing needs a
nonlinear integer-extraction step (a sign, an exp(2πi·)-class), and the inventory of
proven extractions is: (i) the conjugate-pair positivity of §1 (L-side only, line
data); (ii) the deck/monodromy classes (D-side, boundary-analytic, not arithmetic);
(iii) the large-n counting trick (banked; needs a dominating comparison — that is
route #134, not the explicit formula). **No real arithmetic expression with sign
(−1)^N is known; the pairing itself cannot produce one without a comparison
object.** Recorded as the exact shape of the obstruction — the pairing route is not
dead, it is INCOMPLETE-BY-TYPE: it outputs ℝ, the target lives in ℤ/2.

Dead-shaped side note (checked): the Landau nonnegative-coefficient route on the
germ of §3 is capped by the pole — √ζ has a_n ≥ 0 but σ_c = 1 because √ζ ~
(s−1)^{−1/2}; the singularity Landau finds is the pole, not a zero. No information.

## 3. The reroute (GERM): Euler hands us the whole tower as arithmetic

[KNOWN, classical] The Euler product makes ζ formally 2-divisible to every depth:

> ζ(s)^{1/2^k} = ∏_p (1 − p^{−s})^{−1/2^k} = Σ_n a_n^{(k)} n^{−s},
> a^{(k)} multiplicative, a^{(k)}_{p^j} = binom. coeffs of (1−x)^{−1/2^k} ∈ ℤ[1/2],
> convergent on Re s > 1 (for √ζ: a_{p^j} = C(2j,j)/4^j, v₂ = s₂(j) − 2j).

On Re s > 1 every factor of ξ is nonvanishing and the domain is simply connected, so
the 2^k-th roots of ξ exist there and are unique up to μ_{2^k} (banked root
rigidity) — the analytic germ IS the Euler germ up to a constant. Therefore, by the
banked `rhLadder_iff_root`:

> **(GERM) RH_{2^k} ⟺ the Euler germ ξ^{1/2^k} — an explicitly arithmetic object on
> Re s > 1 — continues analytically to Re s > 1/2.**

This is the constraint-not-flow form of the residue question: the arithmetic
supplies the germ (the "bulk candidate"); the constraint is continuability across
the zero field. Classical input ζ ≠ 0 on Re s = 1 already pushes the continuation
frontier strictly inside the strip — the rungs are continuation statements about
the SAME germ, nested. Continuation obstructions are this lab's native machinery
(natural-boundary engines, q62): the lane's open core is now typed as a
continuation problem for a multiplicative-arithmetic germ, not as an estimate.

Cheap Lean target carded: `rhLadder_iff_germ_extends` — repackage
`rhLadder_iff_root` + root rigidity as "the (unique mod μ) root on Re s > 1 extends
to rightHalf". Everything needed is banked.

## 4. Verdict on #133

The pairing cannot output the parity by itself ((SMOOTH), §2) — the task's expected
obstruction is confirmed with its exact shape: integrality must be SUPPLIED by a
comparison object, and the two available suppliers are the dominating truncation
(#134) and the germ continuation (§3). The residue coordinate thus merges with the
germ/annealing coordinates rather than standing alone. Next: (GERM)-Lean packaging,
and the finite convergence of docs 20/22 — read the germ's truncations with the
DISC jet sections.
