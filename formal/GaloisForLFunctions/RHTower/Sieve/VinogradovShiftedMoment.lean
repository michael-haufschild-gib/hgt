import GaloisForLFunctions.RHTower.Sieve.VinogradovMeanValueBound

namespace RHTower.Sieve

noncomputable section

abbrev VinogradovShiftedModSolution
    (q N b k : ℕ) [NeZero q] (l : Fin k → ZMod q) :=
  {uv : (Fin b → Fin N) × (Fin b → Fin N) //
    vinogradovPowerSignatureMod q k uv.1 =
      vinogradovPowerSignatureMod q k uv.2 + l}

theorem card_vinogradovShiftedModSolution_eq_correlation
    {q N b k : ℕ} [NeZero q] (l : Fin k → ZMod q) :
    Fintype.card (VinogradovShiftedModSolution q N b k l) =
      finiteFiberCorrelation
        (vinogradovPowerSignatureMod q k :
          (Fin b → Fin N) → Fin k → ZMod q) l := by
  exact (finiteFiberCorrelation_eq_card
    (vinogradovPowerSignatureMod q k :
      (Fin b → Fin N) → Fin k → ZMod q) l).symm

theorem card_vinogradovShiftedModSolution_le_energy
    {q N b k : ℕ} [NeZero q] (l : Fin k → ZMod q) :
    Fintype.card (VinogradovShiftedModSolution q N b k l) ≤
      finiteFiberEnergy
        (vinogradovPowerSignatureMod q k :
          (Fin b → Fin N) → Fin k → ZMod q) := by
  rw [card_vinogradovShiftedModSolution_eq_correlation]
  exact finiteFiberCorrelation_le_energy _ l

theorem card_vinogradovShiftedModSolution_le_moment
    {q N b k : ℕ} [NeZero q] (hN : N ≠ 0)
    (hq : 2 * b * N ^ k < q) (l : Fin k → ZMod q) :
    Fintype.card (VinogradovShiftedModSolution q N b k l) ≤
      Fintype.card (VinogradovDiagonalSolution N b k) := by
  calc
    _ ≤ finiteFiberEnergy
        (vinogradovPowerSignatureMod q k :
          (Fin b → Fin N) → Fin k → ZMod q) :=
      card_vinogradovShiftedModSolution_le_energy l
    _ = Fintype.card (VinogradovDiagonalSolution N b k) :=
      vinogradovModularMomentAt_eq_card_of_large hN hq

/-- Every modular power-difference fibre at Route-T moment order is bounded
by the closed PNT-free mean-value estimate. -/
theorem card_vinogradovRouteT_shiftedModSolution_le
    {q N s : ℕ} [NeZero q] (hs : 1 ≤ s) (hN : N ≠ 0)
    (hq : 2 * (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s) *
      N ^ (vinogradovRouteTOrder s) < q)
    (l : Fin (vinogradovRouteTOrder s) → ZMod q) :
    Fintype.card (VinogradovShiftedModSolution q N
        (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s)
        (vinogradovRouteTOrder s) l) ≤
      vinogradovMeanConstant
          (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) *
        N ^ (2 * vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s -
            vinogradovRouteTOrder s * (vinogradovRouteTOrder s + 1) / 2 +
          (350 * s + 2)) := by
  exact (card_vinogradovShiftedModSolution_le_moment hN hq l).trans
    (vinogradovRouteT_mean_value_bound hs hN)

end

end RHTower.Sieve
