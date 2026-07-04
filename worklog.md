
## 2026-07-04 (cont.) — (K1) machine-checked: DictionarySign.lean

The seam-continuation lemma dissolved: the mirror-chart choice (Schwarz reflection
through the critical line) replaces path continuation entirely. New module
DictionarySign.lean (build 8588 jobs, axiom-clean [propext, Classical.choice,
Quot.sound], lint green): `xi_deckClass_eq_sign_product` — deck class of ANY root pair
on a mirror-symmetric cover = sign Ξ(p₊)·sign Ξ(p₋) — plus mirrorRoot machinery
(analyticity, root property, Ξ-reality) and the generic pointwise version. Also added
`sq_conj_ratio_of_pos/neg` to DictionaryBase.lean. Doc 33 §4 appended. #131 item (2)
DONE; remaining #131: item (3) — (K2) seam-product chain (`seam_jump` along a finite
crossing list) + the odd-count clause wiring. Board otherwise unchanged: card 1→2
constants write-out (docs 29–31 + 34), doc 30 ledger identity + Thm A + counting lemma
(Lean), exp-family instance run.

## 2026-07-04 (cont.) — (K1) count clause: xi_sign_product_eq_parity

Second DictionarySign increment (build 8588, axiom-clean, lint green): the odd-count
clause composed from the two deck-class evaluations — sign product (new §4 theorem) and
enclosed-order count (deckClass_multi_zero) — via the mirror-chart identification
lineReflect⁻¹(chartRA) = chartLA at critical-line centers (w ↦ −w̄ on the recentered
variable). (K1) fully machine-checked: deck class = sign Ξ(p₊)·sign Ξ(p₋) = (−1)^{Σmᵢ}.
#131 remaining: (K2) seam-product chain only. Board: (K2), card 1→2 constants
write-out, doc 30 ledger identity + Thm A + counting lemma (Lean), exp-family run.

## 2026-07-04 (cont.) — (K2) base: xi_sign_product_eq_onLine_parity

Third DictionarySign increment (8588 jobs, axiom-clean, lint green): sign product =
(−1)^{L(W)} — on-line count only — by composing the parity theorem with
window_identity; off-line mirror pairs cancel mod 2. Dictionary k = 1 layer COMPLETE
(sign reading + total parity + on-line parity). #131 residual narrowed to one decision:
level-4 seam chain (mod-4 reading) vs. germ-extension consumption path (#137) — check
doc 22's reduction wiring first. Board otherwise: card 1→2 constants write-out, doc 30
ledger identity + Thm A + counting lemma (Lean), exp-family run.

## 2026-07-04 (cont.) — #131 CLOSED: dictionary complete + maximality no-go

Decision unit: read doc 22 §2's consumption path (needs L mod 4 under domination),
attacked it, and found the closure is a NO-GO: deckClass_blind_to_split (Lean,
axiom-clean, 8588 jobs, lint green) — deck classes at every level see only the total
enclosed order, so deck+sign data cannot separate a near-line mirror pair from an
on-line pair (the two differ by exactly an N-parity flip). Hence no level-4 seam chain
can carry the mod-4 bit; the DISC discriminant reading is the MINIMAL missing
instrument and the bridge's routing through (SPUR-R) exactness is forced. Doc 33 §7
appended; #131 completed. Sole load-bearing open item of the chain: (S-mono)/(SPUR-R)
constants write-out (#135/#138, card 1→2 gate) + doc 30 ledger identity/Thm A/counting
lemma Lean queue (#143) + exp-family instance run.
