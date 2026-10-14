import GaloisForLFunctions.HTGeometry.GenealogyTailProfile
import GaloisForLFunctions.HTGeometry.CertificateGenealogyTailRecovery

/-! # Exact constructive range of native completed-tail determinants

Every strictly decreasing real profile with boundary value one is realized by
an original positive certificate stream with Hilbert–Schmidt weight. The stream
is constructed from the inverse formula; backward uniqueness proves the actual
determinant identification. Its coefficient function, rather than its auxiliary
bound field, is unique.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap Filter Topology

private theorem positive_coefficient_norm (a : CertStream) (n : ℕ) : ‖(a.c n : ℂ)‖ = a.c n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.pos n)]

private theorem tail_recurrence (a : CertStream) (ha : IsHilbertSchmidt a.weight) (n : ℕ) :
    scalarCertificateTailValue a n = scalarCertificateTailValue a (n + 1) +
      a.c n ^ 2 / 4 * (2 * scalarCertificateTailValue a (n + 1) -
        scalarCertificateTailValue a (n + 2)) := by
  have hs := (scalarCertificate_weight_isHilbertSchmidt_iff a).mp ha
  have hw : Summable (fun n => ‖(a.c n : ℂ)‖ ^ 2) := by
    simpa only [positive_coefficient_norm] using hs
  simpa only [scalarCertificateTailValue_eq a hs, positive_coefficient_norm] using
    normalizedGenealogyTailValue_recurrence (fun n => (a.c n : ℂ)) hw n

private theorem tail_strictAnti (a : CertStream) (ha : IsHilbertSchmidt a.weight) :
    StrictAnti (scalarCertificateTailValue a) := by
  have h := (scalarCertificateTailRecovery_iff a).mpr ha
  apply strictAnti_nat_of_succ_lt
  intro n
  have hd := (h.1 n).2.1
  have he := (eq_div_iff (by linarith :
    2 * scalarCertificateTailValue a (n + 1) - scalarCertificateTailValue a (n + 2) ≠ 0)).mp
      (h.1 n).2.2
  have hp := mul_pos (sq_pos_of_pos (a.pos n)) (show
    0 < 2 * scalarCertificateTailValue a (n + 1) - scalarCertificateTailValue a (n + 2) by linarith)
  nlinarith

def certificateOfTailProfile (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) : CertStream where
  c := genealogyProfileCoefficient Z
  pos := genealogyProfileCoefficient_pos hZ hlim
  bound := Real.sqrt (4 * (Z 0 - 1))
  le_bound := genealogyProfileCoefficient_bound hZ.antitone hlim

@[simp] theorem certificateOfTailProfile_coefficient (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) :
    (certificateOfTailProfile Z hZ hlim).c n = genealogyProfileCoefficient Z n := rfl

theorem certificateOfTailProfile_hilbertSchmidt (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) : IsHilbertSchmidt (certificateOfTailProfile Z hZ hlim).weight :=
  (scalarCertificate_weight_isHilbertSchmidt_iff _).mpr
    (genealogyProfileCoefficient_summable_sq hZ.antitone hlim)

theorem certificateOfTailProfile_energy_le (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) :
    (∑' n, (certificateOfTailProfile Z hZ hlim).c n ^ 2) ≤ 4 * (Z 0 - 1) := by
  simpa only [certificateOfTailProfile_coefficient, genealogyProfileCoefficient_sq hZ.antitone hlim]
    using genealogyProfileEnergy_tsum_le hZ.antitone hlim

theorem certificateOfTailProfile_realizes (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) :
    scalarCertificateTailValue (certificateOfTailProfile Z hZ hlim) = Z := by
  let a := certificateOfTailProfile Z hZ hlim
  have ha := certificateOfTailProfile_hilbertSchmidt Z hZ hlim
  apply backward_genealogy_recurrence_unique
    (genealogyProfileEnergy_nonneg hZ.antitone hlim)
    (genealogyProfileEnergy_summable hZ.antitone hlim) ?_
    (genealogyProfile_recurrence hZ.antitone hlim)
    ((scalarCertificateTailRecovery_iff a).mpr ha).2 hlim
  intro n
  have hc : a.c n ^ 2 = genealogyProfileEnergy Z n :=
    genealogyProfileCoefficient_sq hZ.antitone hlim n
  simpa only [hc] using tail_recurrence a ha n

theorem scalarCertificateTailProfile_iff (Z : ℕ → ℝ) :
    (∃ a : CertStream, IsHilbertSchmidt a.weight ∧ scalarCertificateTailValue a = Z) ↔
      StrictAnti Z ∧ Tendsto Z atTop (𝓝 1) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨tail_strictAnti a ha, ((scalarCertificateTailRecovery_iff a).mpr ha).2⟩
  · rintro ⟨hZ, hlim⟩
    exact ⟨certificateOfTailProfile Z hZ hlim, certificateOfTailProfile_hilbertSchmidt Z hZ hlim,
      certificateOfTailProfile_realizes Z hZ hlim⟩

theorem scalarCertificateTailProfile_unique_iff (Z : ℕ → ℝ) :
    (∃ a : CertStream, IsHilbertSchmidt a.weight ∧ scalarCertificateTailValue a = Z ∧
      (∀ n, a.c n = genealogyProfileCoefficient Z n) ∧
      (∑' n, a.c n ^ 2) ≤ 4 * (Z 0 - 1) ∧
      ∀ b : CertStream, IsHilbertSchmidt b.weight → scalarCertificateTailValue b = Z → b.c = a.c) ↔
      StrictAnti Z ∧ Tendsto Z atTop (𝓝 1) := by
  constructor
  · rintro ⟨a, ha, he, _⟩
    exact (scalarCertificateTailProfile_iff Z).mp ⟨a, ha, he⟩
  · rintro ⟨hZ, hlim⟩
    let a := certificateOfTailProfile Z hZ hlim
    have ha := certificateOfTailProfile_hilbertSchmidt Z hZ hlim
    have he := certificateOfTailProfile_realizes Z hZ hlim
    refine ⟨a, ha, he, fun n => rfl, certificateOfTailProfile_energy_le Z hZ hlim, ?_⟩
    intro b hb hbe
    exact ((scalarCertificateTailValue_classifies b a).mp
      ⟨hb, ha, fun k => congrFun (hbe.trans he.symm) k⟩).2

theorem scalarCertificateTailProfile_roundtrip (a : CertStream) :
    IsHilbertSchmidt a.weight ↔
      ∃ (hZ : StrictAnti (scalarCertificateTailValue a))
        (hlim : Tendsto (scalarCertificateTailValue a) atTop (𝓝 1)),
        IsHilbertSchmidt (certificateOfTailProfile (scalarCertificateTailValue a) hZ hlim).weight ∧
        a.c = (certificateOfTailProfile (scalarCertificateTailValue a) hZ hlim).c := by
  constructor
  · intro ha
    have hZ := tail_strictAnti a ha
    have hlim := ((scalarCertificateTailRecovery_iff a).mpr ha).2
    have hb := certificateOfTailProfile_hilbertSchmidt _ hZ hlim
    have he := certificateOfTailProfile_realizes _ hZ hlim
    exact ⟨hZ, hlim, hb, ((scalarCertificateTailValue_classifies _ _).mp
      ⟨ha, hb, fun k => (congrFun he k).symm⟩).2⟩
  · rintro ⟨hZ, hlim, hb, he⟩
    apply (scalarCertificate_weight_isHilbertSchmidt_iff a).mpr
    have hs := (scalarCertificate_weight_isHilbertSchmidt_iff _).mp hb
    simpa only [he] using hs

end
end GaloisForLFunctions.HTGeometry
