import GaloisForLFunctions.HTGeometry.CertificateGenealogyTailCompression
import GaloisForLFunctions.HTGeometry.PaperGenealogyDeterminantGauge

/-! # Complete coefficient recovery from native infinite-tail determinants

Three consecutive completed tails recover each squared coefficient with a
uniformly positive denominator. The positive stream is recovered exactly; the
complex scalar stream is recovered up to the same full-carrier phase gauge as
its finite Gram determinants. All native completion criteria are equivalences.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap Filter Topology
open scoped ComplexConjugate

private theorem positive_coefficient_norm (a : CertStream) (n : ℕ) : ‖(a.c n : ℂ)‖ = a.c n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.pos n)]

def scalarCertificateTailValue (a : CertStream) (k : ℕ) : ℝ :=
  (scalarCertificateGramCompletion (scalarCertificateTail a k)).re

def paperCertificateTailValue (a : OpCertStream 1) (k : ℕ) : ℝ :=
  (paperGenealogyGramCompletion (paperCertificateTail a k)).re

theorem scalarCertificateTailValue_eq (a : CertStream)
    (hs : Summable (fun n => a.c n ^ 2)) (k : ℕ) :
    scalarCertificateTailValue a k = normalizedGenealogyTailValue (fun n => (a.c n : ℂ)) k := by
  rw [scalarCertificateTailValue, scalarCertificateTailGram_eq a hs, Complex.ofReal_re]

theorem paperCertificateTailValue_eq (a : OpCertStream 1)
    (hs : Summable (fun n => ‖scalarCertificateCoefficient a n‖ ^ 2)) (k : ℕ) :
    paperCertificateTailValue a k = normalizedGenealogyTailValue (scalarCertificateCoefficient a) k := by
  rw [paperCertificateTailValue, paperCertificateTailGram_eq a hs, Complex.ofReal_re]

theorem scalarCertificateTailRecovery_iff (a : CertStream) :
    ((∀ k,
      ((scalarCertificateGramCompletion (scalarCertificateTail a k)).im = 0 ∧
        1 ≤ scalarCertificateTailValue a k ∧
        Tendsto (scalarCertificateNormalizedGram (scalarCertificateTail a k)) atTop
          (𝓝 (scalarCertificateGramCompletion (scalarCertificateTail a k)))) ∧
      1 ≤ 2 * scalarCertificateTailValue a (k + 1) - scalarCertificateTailValue a (k + 2) ∧
      a.c k ^ 2 = 4 * (scalarCertificateTailValue a k - scalarCertificateTailValue a (k + 1)) /
        (2 * scalarCertificateTailValue a (k + 1) - scalarCertificateTailValue a (k + 2))) ∧
      Tendsto (scalarCertificateTailValue a) atTop (𝓝 1)) ↔ IsHilbertSchmidt a.weight := by
  constructor
  · rintro ⟨h, _⟩
    apply (scalarCertificateGramCompletion_hilbertSchmidt_iff a).mp
    simpa only [scalarCertificateTailValue, scalarCertificateTail_zero] using (h 0).1
  · intro h
    have hs := (scalarCertificate_weight_isHilbertSchmidt_iff a).mp h
    have hw : Summable (fun n => ‖(a.c n : ℂ)‖ ^ 2) := by
      simpa only [positive_coefficient_norm] using hs
    refine ⟨?_, ?_⟩
    · intro k
      have hk : Summable (fun n => (scalarCertificateTail a k).c n ^ 2) :=
        (summable_nat_add_iff (f := fun n => a.c n ^ 2) k).mpr hs
      refine ⟨(scalarCertificateGramCompletion_iff _).mpr hk, ?_, ?_⟩
      · simpa only [scalarCertificateTailValue_eq a hs] using
          normalizedGenealogyTailValue_denominator (fun n => (a.c n : ℂ)) hw k
      · simpa only [scalarCertificateTailValue_eq a hs, positive_coefficient_norm] using
          normalizedGenealogyTailValue_recovers_norm_sq (fun n => (a.c n : ℂ)) hw k
    · have he := funext (scalarCertificateTailValue_eq a hs)
      rw [he]
      exact normalizedGenealogyTailValue_tendsto_one _ hw

theorem paperCertificateTailRecovery_iff (a : OpCertStream 1) :
    ((∀ k,
      ((paperGenealogyGramCompletion (paperCertificateTail a k)).im = 0 ∧
        1 ≤ paperCertificateTailValue a k ∧
        Tendsto (paperGenealogyNormalizedGram (paperCertificateTail a k)) atTop
          (𝓝 (paperGenealogyGramCompletion (paperCertificateTail a k)))) ∧
      1 ≤ 2 * paperCertificateTailValue a (k + 1) - paperCertificateTailValue a (k + 2) ∧
      ‖scalarCertificateCoefficient a k‖ ^ 2 =
        4 * (paperCertificateTailValue a k - paperCertificateTailValue a (k + 1)) /
          (2 * paperCertificateTailValue a (k + 1) - paperCertificateTailValue a (k + 2))) ∧
      Tendsto (paperCertificateTailValue a) atTop (𝓝 1)) ↔ IsHilbertSchmidt (1 - a.genealogy) := by
  constructor
  · rintro ⟨h, _⟩
    apply (paperGenealogyGramCompletion_hilbertSchmidt_iff a).mp
    simpa only [paperCertificateTailValue, paperCertificateTail_zero] using (h 0).1
  · intro h
    have hs := (paperGenealogy_weight_isHilbertSchmidt_iff a).mp h
    refine ⟨?_, ?_⟩
    · intro k
      have hk : Summable (fun n => ‖scalarCertificateCoefficient (paperCertificateTail a k) n‖ ^ 2) :=
        (summable_nat_add_iff (f := fun n => ‖scalarCertificateCoefficient a n‖ ^ 2) k).mpr hs
      refine ⟨(paperGenealogyGramCompletion_iff _).mpr hk, ?_, ?_⟩
      · simpa only [paperCertificateTailValue_eq a hs] using
          normalizedGenealogyTailValue_denominator (scalarCertificateCoefficient a) hs k
      · simpa only [paperCertificateTailValue_eq a hs] using
          normalizedGenealogyTailValue_recovers_norm_sq (scalarCertificateCoefficient a) hs k
    · have he := funext (paperCertificateTailValue_eq a hs)
      rw [he]
      exact normalizedGenealogyTailValue_tendsto_one _ hs

theorem scalarCertificateTailValue_classifies (a b : CertStream) :
    (IsHilbertSchmidt a.weight ∧ IsHilbertSchmidt b.weight ∧
      ∀ k, scalarCertificateTailValue a k = scalarCertificateTailValue b k) ↔
      (IsHilbertSchmidt a.weight ∧ a.c = b.c) := by
  constructor
  · rintro ⟨ha, hb, he⟩
    refine ⟨ha, funext fun k => ?_⟩
    have hsa := (scalarCertificate_weight_isHilbertSchmidt_iff a).mp ha
    have hsb := (scalarCertificate_weight_isHilbertSchmidt_iff b).mp hb
    have hwa : Summable (fun n => ‖(a.c n : ℂ)‖ ^ 2) := by
      simpa only [positive_coefficient_norm] using hsa
    have hwb : Summable (fun n => ‖(b.c n : ℂ)‖ ^ 2) := by
      simpa only [positive_coefficient_norm] using hsb
    have hnorm := (normalizedGenealogyTailValue_eq_iff _ _ hwa hwb).mp
      (fun j => by simpa only [scalarCertificateTailValue_eq a hsa,
        scalarCertificateTailValue_eq b hsb] using he j) k
    simpa only [positive_coefficient_norm] using hnorm
  · rintro ⟨ha, he⟩
    have hsa := (scalarCertificate_weight_isHilbertSchmidt_iff a).mp ha
    have hsb : Summable (fun n => b.c n ^ 2) := by simpa only [he] using hsa
    refine ⟨ha, (scalarCertificate_weight_isHilbertSchmidt_iff b).mpr hsb, ?_⟩
    intro k
    rw [scalarCertificateTailValue_eq a hsa, scalarCertificateTailValue_eq b hsb, he]

theorem paperCertificateTailValue_classifies (a b : OpCertStream 1) :
    (IsHilbertSchmidt (1 - a.genealogy) ∧ IsHilbertSchmidt (1 - b.genealogy) ∧
      ∀ k, paperCertificateTailValue a k = paperCertificateTailValue b k) ↔
      (IsHilbertSchmidt (1 - a.genealogy) ∧
        ∀ n, ‖scalarCertificateCoefficient a n‖ = ‖scalarCertificateCoefficient b n‖) := by
  constructor
  · rintro ⟨ha, hb, he⟩
    have hsa := (paperGenealogy_weight_isHilbertSchmidt_iff a).mp ha
    have hsb := (paperGenealogy_weight_isHilbertSchmidt_iff b).mp hb
    refine ⟨ha, (normalizedGenealogyTailValue_eq_iff _ _ hsa hsb).mp ?_⟩
    intro k
    simpa only [paperCertificateTailValue_eq a hsa, paperCertificateTailValue_eq b hsb] using he k
  · rintro ⟨ha, he⟩
    have hsa := (paperGenealogy_weight_isHilbertSchmidt_iff a).mp ha
    have hsb : Summable (fun n => ‖scalarCertificateCoefficient b n‖ ^ 2) := by
      simpa only [he] using hsa
    refine ⟨ha, (paperGenealogy_weight_isHilbertSchmidt_iff b).mpr hsb, ?_⟩
    intro k
    rw [paperCertificateTailValue_eq a hsa, paperCertificateTailValue_eq b hsb]
    exact (normalizedGenealogyTailValue_eq_iff _ _ hsa hsb).mpr he k

theorem paperCertificateTailValue_eq_iff_phaseGauge (a b : OpCertStream 1) :
    (IsHilbertSchmidt (1 - a.genealogy) ∧ IsHilbertSchmidt (1 - b.genealogy) ∧
      ∀ k, paperCertificateTailValue a k = paperCertificateTailValue b k) ↔
      (IsHilbertSchmidt (1 - a.genealogy) ∧
        ∃ (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1), u 0 = 1 ∧
          (∀ n, scalarCertificateCoefficient b n =
            u n * scalarCertificateCoefficient a n * conj (u (n + 1))) ∧
          b.genealogy = RHTower.unitaryPush (scalarCertificatePhaseUnitary u hu) a.genealogy) := by
  rw [paperCertificateTailValue_classifies, ← paperGenealogyGramDet_eq_iff,
    paperGenealogyGramDet_eq_iff_phaseGauge]

end
end GaloisForLFunctions.HTGeometry
