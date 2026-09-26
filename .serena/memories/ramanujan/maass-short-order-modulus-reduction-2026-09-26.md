# Kernel-checked short-order modulus reduction

Goal remains unproved/unfalsified. No improved actual Hecke exponent.

New leaf: formal/GaloisForLFunctions/RHTower/Sieve/KloostermanShortOrderModuli.lean; namespace RHTower.Sieve. q indexes modulus q+1, matching existing Kloosterman API.
- shortOrderModuli p R: indices of positive divisors of p^r-1 for 1<=r<=R.
- mem_shortOrderModuli_of_dvd supplies literal period-divisibility membership.
- card_shortOrderModuli_le: finite divisor-bound estimate.
- shortOrderModuli_subpower: fixed p>=2,k,epsilon>0 gives C>0 uniform over n with cardinal <= C*(p^n)^epsilon.
- shortOrder_kloosterman_subpower: same type of bound for absolute sums of actual Kloosterman summands over every subset of shortOrderModuli p (k*n), all integer frequencies, all weights with norm <=1/(q+1).

Only elementary totient bound plus proved divisor bound; no Weil or cancellation hypothesis. Scratch source passed after explicit real cast fixed one elaboration ambiguity. Targeted leaf build passed (no umbrella/full build); import wired in RHTower. Imported #print axioms audit for definition + four theorems: propext, Classical.choice, Quot.sound only. No raised resource limits or numerical experiments. All owned processes exited. Global lint failed on unrelated unwired RHTower.XiSymmetricDiscIndexParity, with existing size warnings; do not claim global lint passed.

Whole-route consequence: moduli with ord_c(p)<=k*n for fixed k already have an acceptable subpower absolute contribution. Complement of every such cutoff still requires signed cancellation. This is NOT a Maass Ramanujan proof or a classification of all moduli.

Paper-only AH: complete nonzero-residue mean at odd prime q is (1+q*chi(-1))/(q-1), but a fixed Bessel argument block selects only boundedly many consecutive exponents; ord_q(p)>=log(q+1)/log(p). Full-period cancellation cannot be inserted into the short window. Other AF-AG paper obstructions remain unformalized.

Own research card and facts: docs/drafts/pipeline/1-in-progress/ramanujan-petersson-maass-2026-09-26.md and -facts.md. Latest sections AH-AI. 3,000-conjecture request unfinished.