# FZZ external-BRST branch-charge no-go (2026-09-01)

Formalized source-derived classification from HJ cigar Eqs. 3.16–3.19, 3.29 and BTZ Eqs. 4.26–4.27.

For `m=(p-kν)/2`, `mbar=-(p+kν)/2`, `q=1-2/k`, marked OPE coefficients are `L⁺L=-j/q+m`, `L⁺R=-j/q+mbar`, `L⁻L=-j/q-m`, `L⁻R=-j/q-mbar`. Signed logarithmic branch charges are exactly `(p,-p)`, independent of `j,k,ν`; branch incidence iff `p≠0`. Thus no predicate of complete branch-charge pair on physical `j=-1/2+iP` selects `P=0`. This kills external-BRST branch-incidence/monodromy-only arrow into torus area Ward/passivity/RH.

Positive survivor: even log-modulus mean is `-2j/q` and reconstructs `j` for `k>2`; odd half-difference is `kν`. Live external-BRST work must use full modulus/on-shell kernel, support motion, or higher replica order.

Lean module: `GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBranchChargeNoGo`; capstone `not_exists_physical_fzzCigarExternalBRSTBranchCharge_radialSelector`. Direct Lean and targeted build pass; key axioms `[propext, Classical.choice, Quot.sound]`; umbrella wired. Cards in stage 3 and failed route. Frontier map untouched. Facts ledger updated.