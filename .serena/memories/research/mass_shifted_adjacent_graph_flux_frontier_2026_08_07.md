# Mass-shifted spectral face: C38-C40 frontier (2026-08-07)

Target: docs/reports/mass-shifted-spectral-trace-route.md §9.3. Exact open core remains fixed-line uniform boundedness of valuation-one prime layer S₁,a; equivalent to RH.

Formalized this run:
- XiMassAdjacentPrimeDifference.lean: actual integral Fourier Lipschitz + adjacent balanced atom telescope.
- XiMassAdjacentPrimeMask.lean: reverse-normalized actual mask v_adj(p₂n)=1, v_adj(p₂n₊₁)=-t₂n/t₂n₊₁. Bertrand proves norm ≤2; exact prime-layer/pair-layer equality; uniform bound 32 J₁(σ)E₀.
- XiMassAdjacentPrimeQuotient.lean: adding b v_adj modulo critical-weight ℓ¹ preserves fixed-line boundedness. c=0 bounded; c≠0 iff valuation-one bound/RH. Cross-prime ideal enlarges but scalar survives.
- XiMassFullAdjacentPrimeGraph.lean: every consecutive graph edge G_n=t_{n+1}(F_n-F_{n+1}) is absolutely summable with 16 J₁(σ)(E_n-E_{n+1}); full connected edge layer bounded. Exact finite Abel identity:
  sum_{n<N} t_n F_n = F_{N-1}T_N + sum_{n<N-1}T_{n+1}(F_n-F_{n+1}).
  Therefore missing theorem is cumulative-mass/terminal boundary flux, not more local edges.
- HedenmalmTwoPrimeBezoutGrowthNoGo.lean: algebraic two-prime Bezout generation cannot be bounded synthesis; no uniformly bounded real-axis Bezout pair exists since both centered multipliers tend to zero.

Latest corpus audit:
- Wold normal derivative identifies Λ but critical wall is non-Hilbert–Schmidt.
- Hedenmalm finite/summably weighted diagonal frame coercivity fails by recurrence.
- Two-prime entire ideal is algebraic only; bounded coefficient topology fails (new no-go above).
- Compact theta root-flux energy =0 iff RH: faithful detector, not source-side discharge.
- Suzuki parity complementarity/odd-floor amplification: false-RH detector, no upper bound for Abel flux.
- Band–Kaiser explicit conditions 8m²≤√c and 32m exp(-√c/2)≤1 allow cofinal schedules m(c)→∞ slower than c^(1/4). C40 is the surviving avenue: construct genuinely non-diagonal synthesis of first m(c) Abel-flux coordinates into Kaiser packets with exp(o(c)) conditioning and bounded-ideal tail.

Cards:
- docs/drafts/pipeline/3-formalized/mass-xi-balanced-adjacent-prime-difference-ideal.md
- docs/drafts/pipeline/3-formalized/mass-xi-balanced-adjacent-prime-difference-summability.md
- docs/drafts/pipeline/3-formalized/mass-xi-full-adjacent-prime-graph-flux.md
- docs/drafts/pipeline/3-formalized/hedenmalm-two-prime-bezout-growth-no-go.md
- docs/drafts/pipeline/1-in-progress/mass-xi-cofinal-kaiser-abel-flux-completion.md

Verification: direct lake env lean checks passed; targeted builds of all new modules passed. #print axioms shows only propext, Classical.choice, Quot.sound. Targeted rg found no sorry/admit/axiom/opaque/unsafe. Corpus-wide lint failed only for unrelated concurrently added unreachable modules, not these modules.