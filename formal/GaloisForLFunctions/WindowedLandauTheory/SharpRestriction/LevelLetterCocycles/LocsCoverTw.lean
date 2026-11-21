import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow



noncomputable section

namespace WindowedLandauTheory.MainNotions.N

def LocsCoverTw (D : WindowedLandauTheory.BasicNotions.D7) : Prop := ∀ j' w', 1 ≤ j' → j' ≤ D.R.m → D.what₂.muAt w' ≠ D.what₂.mu0 →
  ∑ i ∈ D.nd.locs j' w', Module.finrank (D.nd.O i) (D.nd.Mt i) =
    Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w') j')

theorem locsCoverTw_of (D : WindowedLandauTheory.BasicNotions.D7) (h : D.nd.LocsCover) : LocsCoverTw D := by
  exact h

end WindowedLandauTheory.MainNotions.N

end

