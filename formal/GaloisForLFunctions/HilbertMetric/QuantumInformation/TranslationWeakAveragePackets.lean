import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationWeakAverage
import GaloisForLFunctions.HTGeometry.FiniteRankCutoffWardTrace
import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Weak translation averages of finite-rank Ward packets

Translation averaging annihilates the existing finite-rank source operators.
For a scalar identity plus a source packet, it extracts the intrinsic scalar
component. Mixed packet Gram averages have an exact formula, are integrable,
and remain positive in every finite auxiliary dimension.
-/

noncomputable section
open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped BigOperators ComplexConjugate ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

private theorem finiteRankProbe_apply {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → Space) (x : Space) :
    HTGeometry.finiteRankProbe c a b x =
      ∑ i, inner ℂ (b i) x • (c i • a i) := by
  simp only [HTGeometry.finiteRankProbe, _root_.sum_apply, smul_apply, rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm (c i) (inner ℂ (b i) x) (a i)

/-- Translated vectors almost surely avoid every fixed finite-rank source packet. -/
theorem finiteRankProbe_shift_ae_zero {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → Space) (v : Space) :
    (fun t : ℝ => HTGeometry.finiteRankProbe c a b (shift t v)) =ᵐ[volume] 0 := by
  have h : ∀ᵐ t ∂volume, ∀ i : Fin n, inner ℂ (shift t v) (b i) = 0 :=
    ae_all_iff.mpr fun i => shift_inner_ae_zero v (b i)
  filter_upwards [h] with t ht
  rw [finiteRankProbe_apply]
  change ∑ i, inner ℂ (b i) (shift t v) • (c i • a i) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [← inner_conj_symm, ht i, map_zero, zero_smul]

/-- A scalar identity perturbed by an existing finite-rank Ward source. -/
def unitizedPacket {n : ℕ} (d : ℂ) (c : Fin n → ℂ)
    (a b : Fin n → Space) : Space →L[ℂ] Space :=
  d • 1 + HTGeometry.finiteRankProbe c a b

private theorem unitizedPacket_shift_ae {n : ℕ} (d : ℂ) (c : Fin n → ℂ)
    (a b : Fin n → Space) (v : Space) :
    (fun t : ℝ => unitizedPacket d c a b (shift t v)) =ᵐ[volume]
      (fun t => d • shift t v) := by
  filter_upwards [finiteRankProbe_shift_ae_zero c a b v] with t ht
  change d • shift t v + HTGeometry.finiteRankProbe c a b (shift t v) = _
  rw [ht, Pi.zero_apply, add_zero]

/-- Actual finite-rank Ward observables have zero normalized translation average. -/
theorem interval_average_finiteRankProbe {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → Space) (u v : Space) :
    ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u)
      (HTGeometry.finiteRankProbe c a b (shift t v)) = 0 := by
  simp_rw [finiteRankProbe_apply]
  exact interval_average_finiteRank (fun i => c i • a i) b u v

/-- Normalized averaging extracts the scalar part of every unitized Ward packet. -/
theorem interval_average_unitizedPacket {n : ℕ} (d : ℂ) (c : Fin n → ℂ)
    (a b : Fin n → Space) (u v : Space) :
    ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u)
      (unitizedPacket d c a b (shift t v)) = d * inner ℂ u v := by
  have h : (fun t : ℝ => inner ℂ (shift t u)
      (unitizedPacket d c a b (shift t v))) =ᵐ[
        volume.restrict (Set.Ioc 0 1)] (fun _ => d * inner ℂ u v) := by
    filter_upwards [ae_restrict_of_ae (unitizedPacket_shift_ae d c a b v)] with t ht
    rw [ht, inner_smul_right, (shift t).inner_map_map]
  rw [integral_congr_ae h]
  simp

private theorem packetGram_ae {n m : ℕ} (d e : ℂ)
    (c : Fin n → ℂ) (a b : Fin n → Space)
    (f : Fin m → ℂ) (p q : Fin m → Space) (u v : Space) :
    (fun t : ℝ => inner ℂ (unitizedPacket d c a b (shift t u))
      (unitizedPacket e f p q (shift t v))) =ᵐ[
        volume.restrict (Set.Ioc 0 1)] (fun _ => conj d * e * inner ℂ u v) := by
  filter_upwards [ae_restrict_of_ae (unitizedPacket_shift_ae d c a b u),
    ae_restrict_of_ae (unitizedPacket_shift_ae e f p q v)] with t ht hs
  rw [ht, hs, inner_smul_left, inner_smul_right, (shift t).inner_map_map]
  ring

/-- Every mixed packet Gram coefficient is integrable on the averaging interval. -/
theorem packetGram_integrableOn {n m : ℕ} (d e : ℂ)
    (c : Fin n → ℂ) (a b : Fin n → Space)
    (f : Fin m → ℂ) (p q : Fin m → Space) (u v : Space) :
    IntegrableOn (fun t : ℝ => inner ℂ (unitizedPacket d c a b (shift t u))
      (unitizedPacket e f p q (shift t v))) (Set.Ioc 0 1) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  exact (integrable_congr (packetGram_ae d e c a b f p q u v)).mpr (integrable_const _)

/-- Averaging mixed packet Grams removes both finite-rank perturbations exactly. -/
theorem interval_average_packetGram {n m : ℕ} (d e : ℂ)
    (c : Fin n → ℂ) (a b : Fin n → Space)
    (f : Fin m → ℂ) (p q : Fin m → Space) (u v : Space) :
    ∫ t : ℝ in Set.Ioc 0 1,
      inner ℂ (unitizedPacket d c a b (shift t u))
        (unitizedPacket e f p q (shift t v)) = conj d * e * inner ℂ u v := by
  rw [integral_congr_ae (packetGram_ae d e c a b f p q u v)]
  simp

/-- The scalar component is intrinsic: two packet descriptions agree exactly componentwise. -/
theorem unitizedPacket_eq_iff {n m : ℕ} (d e : ℂ)
    (c : Fin n → ℂ) (a b : Fin n → Space)
    (f : Fin m → ℂ) (p q : Fin m → Space) :
    unitizedPacket d c a b = unitizedPacket e f p q ↔
      d = e ∧ HTGeometry.finiteRankProbe c a b = HTGeometry.finiteRankProbe f p q := by
  classical
  constructor
  · intro h
    let w : Space := lp.single 2 (0 : ℝ) (1 : ℂ)
    have hw : inner ℂ w w = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      have hn : ‖w‖ = 1 := by
        change ‖(lp.single 2 (0 : ℝ) (1 : ℂ) : Space)‖ = 1
        rw [lp.norm_single (by norm_num), norm_one]
      rw [hn]
      norm_num
    have he := congrArg (fun T : Space →L[ℂ] Space =>
      ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t w) (T (shift t w))) h
    rw [interval_average_unitizedPacket, interval_average_unitizedPacket,
      hw, mul_one, mul_one] at he
    refine ⟨he, ?_⟩
    have hs : e • (1 : Space →L[ℂ] Space) + HTGeometry.finiteRankProbe c a b =
        e • 1 + HTGeometry.finiteRankProbe f p q := by
      simpa only [unitizedPacket, he] using h
    exact add_left_cancel hs
  · rintro ⟨rfl, hk⟩
    rw [unitizedPacket, unitizedPacket, hk]

/-- Packet Gram averaging is positive in every finite auxiliary dimension. -/
theorem interval_average_packetGram_posSemidef {n k : ℕ}
    (d : Fin k → ℂ) (c : Fin k → Fin n → ℂ)
    (a b : Fin k → Fin n → Space) (u : Fin k → Space) :
    Matrix.PosSemidef (fun i j => ∫ t : ℝ in Set.Ioc 0 1,
      inner ℂ (unitizedPacket (d i) (c i) (a i) (b i) (shift t (u i)))
        (unitizedPacket (d j) (c j) (a j) (b j) (shift t (u j)))) := by
  have he : (fun i j => ∫ t : ℝ in Set.Ioc 0 1,
      inner ℂ (unitizedPacket (d i) (c i) (a i) (b i) (shift t (u i)))
        (unitizedPacket (d j) (c j) (a j) (b j) (shift t (u j)))) =
      (fun i j => inner ℂ (d i • u i) (d j • u j)) := by
    funext i j
    rw [interval_average_packetGram, inner_smul_left, inner_smul_right]
    ring
  rw [he]
  exact ((HTGeometry.isPSDKernel_gram (fun i => d i • u i)).posSemidef
    (fun i => i)).transpose

#print axioms finiteRankProbe_shift_ae_zero
#print axioms interval_average_finiteRankProbe
#print axioms interval_average_unitizedPacket
#print axioms packetGram_integrableOn
#print axioms interval_average_packetGram
#print axioms unitizedPacket_eq_iff
#print axioms interval_average_packetGram_posSemidef
end GaloisForLFunctions.HilbertMetric.ShiftAverage
