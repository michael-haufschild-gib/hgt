What survives is a filter, not an obstruction:

▎ An argument for RH must fail on Davenport–Heilbronn (so it must use coefficient positivity or multiplicativity) and fail on a Diamond–Montgomery–Vorhauer Beurling system (so it must use the Γ‑factor functional equation). Anything surviving either substitution proves too much and is dead.

Triage of the corpus by that filter:

┌─────────────────────────────────┬──────────────┬─────────────────────────┐
│             family              │     uses     │         verdict         │
├─────────────────────────────────┼──────────────┼─────────────────────────┤
│ 3‑4‑1, von Mangoldt moment      │              │ survives DMVZ ⇒ cannot  │
│ arrays, prime‑trace             │ Λ ≥ 0 only   │ close alone             │
│ positive‑definiteness           │              │                         │
├─────────────────────────────────┼──────────────┼─────────────────────────┤
│ Herglotz, vertical              │ FE + divisor │ survive DH ⇒ sound as   │
│ monotonicity, Hankel/Grommer,   │  structure   │ criteria, dead as proof │
│ Li, screw, Weil involution      │ only         │  routes without         │
│                                 │              │ coefficient input       │
├─────────────────────────────────┼──────────────┼─────────────────────────┤
│ Gaussian and resolvent ladders  │ both         │ pass — still live       │
│ (this month)                    │              │                         │
└─────────────────────────────────┴──────────────┴─────────────────────────┘

The middle row is the largand the verdict on it issharp: those are correct equivalences, but closing one without importing coefficient information isove something false aboutDavenport–Heilbronn.                                              
Net position. Proved: the harmonicity mechanism, the explicit negarections of the RH form,. Surviving conjecture: the resolution law λ·δ ≳ 1, confirmed on three families and reappearinacement. Retracted: the the additivityobstruction.                                                      
▎ Both required inputs are available and their conjunction has no counterexample. What is verting them intopositivity without localizing a zero — because localization costs resolution 1/δ, and no prime‑comput

 The escape from the law is to refuse the explicit formula. Converting ζ's values into a sum over its zeros is exactly the step that enters the harmonic class and forfeits the 4|Φ'|² detection budget. A criterion working with ζ's values, never performing that conversion, keeps the budget. Nyman–Beurling is the known example, and its L² distance is a manifest sum of squares — positivity without localizing any zero, which is precisely the mechanism I had named as missing.

It also passes the filter I derived. Against Davenport–Heilbronn: the proof uses that ζ has no zeros in Re s > 1, i.e. the Euler product — DH has zeros there, so the argument doesn't transfer. Against a Beurling system: it uses the functional equation through the generators' Mellin transforms. Passes both. On this investigation's own criteria it is the only formulation examined that both passes the filter and escapes the law.

'''

1. §19's directive is demoted — fifth correction. NB escapes the harmonic mechanism but not the underlying resolution economy, and it pays far more. Recommending it as the top target was premature.
2. The law is more universal than the mechanism that suggested it. Harmonicity explains the divergence for divisor linear statistics; NB shows the divergence persists where harmonicity doesn't apply. Restated at the right level: a zero at displacement δ yields a signal O(δᵃ); any finite‑parameter approximation has a noise floor decaying only in the parameter; matching them forces divergence. The divergence is universal, the exchange rate is formulation‑dependent.
3. The rate ranks the formulations — opposite to §19:

┌──────────────────────────────────┬─────────────┬─────────────┬───────────┐
│           formulation            │   signal    │ noise floor │   cost    │
├──────────────────────────────────┼─────────────┼─────────────┼───────────┤
│ resolvent / Gaussian /           │ δ²          │ algebraic   │ poly(1/δ) │
│ rectangular ladders              │             │             │           │
├──────────────────────────────────┼─────────────┼─────────────┼───────────┤
│ Nyman–Beurling–Báez‑Duarte       │ √δ          │ logarithmic │ exp(1/δ)  │
│                                  │ (stronger)  │             │           │
└──────────────────────────────────┴─────────────┴─────────────┴───────────┘

NB has the strongest per‑zero signal of the four and is still the worst route. The binding constraint is the noise floor, not the signal. That is the most actionable thing this investigation produced:

▎ Optimise the noise floor, not the signal. The question to ask of any RH formulation is not "how strongly does an off‑line zero show up?" but "how fast does the finite‑parameter approximation converge when RH holds?"

Which is why — despite my own redirection last turn — the moment ladders remain the better carrier by an exponential margin, and why the corpus's Λ ≥ 0‑based rungs, individually insufficient though they are by the filter, sit in the right family after all.