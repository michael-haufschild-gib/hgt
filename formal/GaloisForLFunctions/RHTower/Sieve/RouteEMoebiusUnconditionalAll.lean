import GaloisForLFunctions.RHTower.Sieve.RouteEMoebiusUnconditional
import GaloisForLFunctions.RHTower.Sieve.TwoRangeAssembly

/-!
# Route E at every fixed subpower window

The two-range Möbius theorem supplies the sole analytic input of the existing Route E
sign-density assembly for every window `exp((log x)^beta)` with `0 < beta < 1`.
-/

namespace RHTower.Sieve

open Filter Topology ArithmeticFunction

noncomputable section

/-- **Route E's coprime squarefree sign density at every fixed subpower window.** -/
theorem route_e_sign_density_unconditional_all {beta : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {s : Int}
    (hs : s = 1 ∨ s = -1) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2
          - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - epsilon
        ≤ coprimeSignClassCount x (cardLength beta x) s
          / (cardLength beta x * Real.sqrt x * Real.log 2) :=
  route_e_sign_density_of_moebius_averaged hs
    (tendsto_cardLength_div_logLog hbeta0)
    (cardLength_le_sqrt hbeta0 hbeta1)
    (averagedMeanSquare_moebius_cardLength_all hbeta0 hbeta1) hepsilon

/-- **Both coprime squarefree product-sign classes occur at every fixed subpower window.** -/
theorem route_e_signClass_nonempty_unconditional_all {beta : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {s : Int}
    (hs : s = 1 ∨ s = -1) :
    ∀ᶠ x in atTop, (coprimeSignClass x (cardLength beta x) s).Nonempty :=
  route_e_signClass_nonempty_of_moebius_averaged hs
    (tendsto_cardLength_div_logLog hbeta0)
    (cardLength_le_sqrt hbeta0 hbeta1)
    (averagedMeanSquare_moebius_cardLength_all hbeta0 hbeta1)

end

end RHTower.Sieve
