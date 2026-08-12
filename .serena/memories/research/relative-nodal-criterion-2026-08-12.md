# Step 46: the relative nodal criterion — RH beyond any verification height [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/XiResolventRelativeNodalCriterion.lean` (imports
XiResolventTailSurrogate), wired last in the RHTower chain. Five theorems, all
[propext, Classical.choice, Quot.sound].

## The endpoint

`riemannHypothesis_iff_partial_line_and_relative_nodal {X δ} (hX : 0 ≤ X) (P : Polynomial ℝ)
(hPnz : ∀ q, ‖u_q‖ < δ → evalRealPolynomial P (u_q) ≠ 0)`:
RH ⟺ (∀ q, δ ≤ ‖u_q‖ → im(spectral) = 0) ∧ (∀ R : Finset ℝ ⊂ (0,1], ∀ m,
0 ≤ Re minor(0,2,1) at `X^m * (nodalPolynomial R * P)`).

For ANY scale δ and ANY alive-below-scale P: one verified scale converts RH into the countable
RELATIVE list. The `(p·P)²`-weighted moments are supported on the sub-δ copies
(`xiPolyMoment_mul_eq_tsum_subtype_of_kill`, via `tsum_subtype_eq_of_support_subset`) — the
relative list lives entirely on the truncated divisor.

## The bootstrap no-go

`eval_norm_mul_kill_eq_zero_of_line`: under hline, `Polynomial.eval ‖u_{q₁}‖ (p * P) = 0` for
every witness above scale and every multiple of a killing P — the two-scale supply's witness
expression vanishes identically on the certificate family. Supply polynomials (alive at the
on-line spectrum) and certificate polynomials (dead above the working level) are DISJOINT
families: no self-improvement circle exists in this representation.

## Proof shape (backward)

Step-40b descent clone: strong induction on ncard of higher-modulus copies; short-circuit
`by_cases δ ≤ ‖u q‖ → hline`; hIH also case-splits on δ; atoms = ALL above-ℓ norms (real: ≥ δ
by hline, (ℓ,δ) by IH); weight W := (nodalPolynomial atoms * P); hkill via nodal factor
(Finset.prod_eq_zero), hnz via mul_eq_zero rcases (nodal: node > ℓ = |u| contradiction; P:
hPnz since level < δ); even machine + index shift consume hdata at R = atoms. Forward via
`xiSpectralPoint_real_of_rh` (∃ t, spectral = ↑t) and the all-p forward theorem.

## Significance

The gap to an RH proof is now formally factored scale-by-scale: [any verified height T] gives
hline(δ(T)); the remainder is exactly the relative list — countable, explicit, living on the
truncated spectrum, NOT feedable by two-scale supply (needs sub-δ-native mechanisms). All
effective machinery (windows 39-40, masking 38, delay 43, surrogate 45, budget 44) applies to
the truncated world verbatim.

## Next

(i) effective theory inside the truncated world — relative windows with the sub-δ mass bounded
by the tail surrogate (ray jets): first quantitative handle on the relative list; (ii)
certified numeric ray jets via Γ/ζ decomposition (digamma from mathlib convexOn_log_Gamma,
ζ'/ζ from von Mangoldt LSeries — heavy, multi-batch); (iii) P-relative masking no-go
(sharpness of the relative family). Card: xic-order-one-growth-organ.md step 46.
