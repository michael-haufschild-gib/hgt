import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy

/-!
# Hasse reconstruction for clock holonomy

For a reversible group-valued edge calibration on a connected graph, the closed-walk readings
form a complete local obstruction packet.  Unit reading at every loop reconstructs a global
potential, unique after one basepoint normalization.  Without normalization, all potentials differ
by one common left factor.  Failure of global exactness therefore has an explicit nonunit loop
witness.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v
variable {V : Type u} {A : Type v}

/-- Two global potentials for the same calibration agree everywhere once they agree at one
basepoint. -/
theorem clockCalibrationPotential_eq_of_eq_at {G : SimpleGraph V} [Group A]
    (hG : G.Connected) (c : V → V → A) (g h : V → A)
    (hg : ∀ {u w}, G.Adj u w → c u w = (g u)⁻¹ * g w)
    (hh : ∀ {u w}, G.Adj u w → c u w = (h u)⁻¹ * h w)
    {root : V} (hroot : g root = h root) :
    g = h := by
  funext v
  let p : G.Walk root v := Classical.choice (hG root v)
  have hgt := clockWalkTransport_of_exact c g hg p
  have hht := clockWalkTransport_of_exact c h hh p
  have heq : (g root)⁻¹ * g v = (h root)⁻¹ * h v := hgt.symm.trans hht
  calc
    g v = g root * ((g root)⁻¹ * g v) := by group
    _ = g root * ((h root)⁻¹ * h v) := by rw [heq]
    _ = h root * ((h root)⁻¹ * h v) := by rw [hroot]
    _ = h v := by group

/-- The only ambiguity in a global potential is multiplication of every vertex value by one
common left factor. -/
theorem clockCalibrationPotentials_commonLeftFactor {G : SimpleGraph V} [Group A]
    (hG : G.Connected) (c : V → V → A) (g h : V → A)
    (hg : ∀ {u w}, G.Adj u w → c u w = (g u)⁻¹ * g w)
    (hh : ∀ {u w}, G.Adj u w → c u w = (h u)⁻¹ * h w) :
    ∃! a : A, h = fun v => a * g v := by
  let root : V := Classical.choice hG.nonempty
  refine ⟨h root * (g root)⁻¹, ?_, ?_⟩
  · funext v
    let p : G.Walk root v := Classical.choice (hG root v)
    have hgt := clockWalkTransport_of_exact c g hg p
    have hht := clockWalkTransport_of_exact c h hh p
    have heq : (g root)⁻¹ * g v = (h root)⁻¹ * h v := hgt.symm.trans hht
    calc
      h v = h root * ((h root)⁻¹ * h v) := by group
      _ = h root * ((g root)⁻¹ * g v) := by rw [← heq]
      _ = (h root * (g root)⁻¹) * g v := by group
  · intro a ha
    have haroot := congrFun ha root
    calc
      a = (a * g root) * (g root)⁻¹ := by group
      _ = h root * (g root)⁻¹ := by rw [← haroot]

/-- **Normalized clock Hasse reconstruction.**  All local loop holonomies are one exactly when
they reconstruct one unique global potential whose chosen basepoint value is one. -/
theorem clockCalibrationFlat_iff_existsUnique_normalizedPotential
    {G : SimpleGraph V} [Group A] (hG : G.Connected) (c : V → V → A)
    (hrev : ClockCalibrationReversible G c) (root : V) :
    ClockCalibrationFlat G c ↔
      ∃! g : V → A,
        g root = 1 ∧ ∀ {u w}, G.Adj u w → c u w = (g u)⁻¹ * g w := by
  constructor
  · intro hflat
    obtain ⟨g, hg⟩ := clockCalibrationExact_of_flat hG c hrev hflat
    let gn : V → A := fun v => (g root)⁻¹ * g v
    have hgnroot : gn root = 1 := by
      simp [gn]
    have hgn : ∀ {u w}, G.Adj u w → c u w = (gn u)⁻¹ * gn w := by
      intro u w huw
      rw [hg huw]
      simp only [gn]
      group
    refine ⟨gn, ⟨hgnroot, hgn⟩, ?_⟩
    intro h hh
    apply clockCalibrationPotential_eq_of_eq_at hG c h gn hh.2 hgn
    rw [hh.1, hgnroot]
  · rintro ⟨g, hg, _⟩
    exact clockCalibrationFlat_of_exact c ⟨g, hg.2⟩

/-- Global exactness is equivalent to unique normalized reconstruction from its edge ratios. -/
theorem clockCalibrationExact_iff_existsUnique_normalizedPotential
    {G : SimpleGraph V} [Group A] (hG : G.Connected) (c : V → V → A)
    (hrev : ClockCalibrationReversible G c) (root : V) :
    ClockCalibrationExact G c ↔
      ∃! g : V → A,
        g root = 1 ∧ ∀ {u w}, G.Adj u w → c u w = (g u)⁻¹ * g w := by
  rw [clockCalibrationExact_iff_flat hG c hrev]
  exact clockCalibrationFlat_iff_existsUnique_normalizedPotential hG c hrev root

/-- **Complete local obstruction witness.**  A reversible connected calibration is not globally
exact exactly when some closed walk has nonunit holonomy. -/
theorem not_clockCalibrationExact_iff_exists_nontrivial_closedHolonomy
    {G : SimpleGraph V} [Group A] (hG : G.Connected) (c : V → V → A)
    (hrev : ClockCalibrationReversible G c) :
    ¬ ClockCalibrationExact G c ↔
      ∃ u : V, ∃ p : G.Walk u u, clockWalkTransport c p ≠ 1 := by
  rw [clockCalibrationExact_iff_flat hG c hrev]
  simp only [ClockCalibrationFlat]
  push Not
  rfl

end GaloisForLFunctions.HTGeometry
