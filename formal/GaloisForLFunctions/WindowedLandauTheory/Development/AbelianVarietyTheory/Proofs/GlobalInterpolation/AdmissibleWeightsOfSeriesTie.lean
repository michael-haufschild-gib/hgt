import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetWeightLower
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetWeightSquarefree
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraWeightSquarefree
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypesCompatibility

/-! Identifying the host's central series idempotents with polynomial
Harish–Chandra series gives the required bounds on the host weights. -/

noncomputable section
open Polynomial WindowedLandauTheory.BasicNotions
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open WindowedLandauTheory.NormalizedTypes
open scoped Classical

namespace GlobalTheory.GLq

private theorem five_le_typePrime (D : D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        (((pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd).mul_right _).mul_right _), hc]
  have := (D.host.g_prime k).two_le
  omega

private theorem rank_eq_k_add_two_mul (R : Ranks) :
    R.r = R.k + 2 * (R.m / 2 - 1) + 1 := by
  obtain ⟨a, ha⟩ := R.m_even
  have := R.two_le_m
  unfold Ranks.r
  omega

private theorem admissibleLabelWeights_of_relabelled_series (D : D7)
    (hD : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ (L : LabelDatum (D.host.g k)) (σ π : (ZMod (D.host.g k))[X] → (ZMod (D.host.g k))[X]),
        (∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P) ∧ π (σ P) = P) ∧
        ∀ f, IsLabel D k f → D.ntypes.eSer k f = eSerC L D.R.r (relabelPolynomial σ f)) :
    admLq D := by
  intro k ψ hψ
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, σ, π, hσ, hL⟩ := hD k
  have hw (a : MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)) (f : (ZMod (D.host.g k))[X])
      (hf : IsLabel D k f) : wtOf D k a f = wtC L a (relabelPolynomial σ f) := by
    unfold wtOf wtC
    rw [hL f hf]
  have hz (a : MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)) (f : (ZMod (D.host.g k))[X])
      (hf : ¬ IsLabel D k f) : wtOf D k a f = 0 := by
    unfold wtOf
    rw [D.ntypes.eSer_zero k f hf]
    simp
  have h5 := five_le_typePrime D k
  let s := D.R.m / 2 - 1
  have hr : D.R.r = D.R.k + 2 * s + 1 := rank_eq_k_add_two_mul D.R
  have hk : 0 < D.R.k := by
    have := D.R.m_add_three_le_k
    omega
  have hks : s + D.R.k < D.R.r := by omega
  obtain ⟨hU, hU1⟩ := eU_mul_self_coeff_one (n := D.R.r) ψ
  obtain ⟨hJ, hJ1⟩ := eJ_mul_self_coeff_one ψ D.R.k s hks
  have hU0 : 0 ≤ ((eU (D.host.g k) D.R.r ψ).coeff 1).re := by
    rw [hU1, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  have hJ0 : 0 ≤ ((eJ (D.host.g k) D.R.r D.R.k s ψ).coeff 1).re := by
    rw [hJ1]
    simp only [← Complex.ofReal_natCast (D.host.g k), ← Complex.ofReal_pow,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  simp only [eUk, eJk]
  refine ⟨fun f => ?_, fun f hf hs => ?_, fun f hf => ?_, fun f hf hs => ?_⟩
  · by_cases hf : IsLabel D k f
    · rw [hw _ f hf, hw _ f hf]
      exact ⟨wtC_nonneg_of_idempotent L _ hU hU0 _, wtC_nonneg_of_idempotent L _ hJ hJ0 _⟩
    · rw [hz _ f hf, hz _ f hf]
      exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨hm, hd, h0, hsq⟩ := relabelPolynomial_properties hσ hf.1 hf.2.2
    rw [hw _ f hf, wtC_eU_squarefree L h5 ψ hψ _ hm (hd.trans hf.2.1) h0 (hsq hs),
      normalizedFactors_relabel_prod_degree (fun d => (D.host.g k : ℝ) ^ d - 1) hf.2.2
        (fun d P hP => (hσ d P hP).1)]
  · rw [hw _ f hf, hw _ f hf]
    simpa only [one_div] using wtC_eJ_lower L ψ hψ D.R.k s hr hk (relabelPolynomial σ f)
  · obtain ⟨hm, hd, h0, hsq⟩ := relabelPolynomial_properties hσ hf.1 hf.2.2
    rw [hw _ f hf, hw _ f hf]
    exact wtC_eJ_upper_squarefree L h5 ψ hψ D.R.k s hr _ hm (hd.trans hf.2.1) h0 (hsq hs)

/-- Direct identification with the Green series gives admissible weights. -/
theorem admissibleLabelWeights_of_eSerTie (D : D7) (hD : ESerTie D) : admLq D := by
  apply admissibleLabelWeights_of_relabelled_series D
  intro k
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, _, hL⟩ := hD k
  refine ⟨L, id, id, fun _ _ hP => ⟨hP, rfl⟩, fun f hf => ?_⟩
  rw [relabelPolynomial_id hf.1]
  exact hL f

/-- The normalized local types give admissible weights after permuting the
prime labels in each degree. -/
theorem _root_.GlobalTheory.Top.Lq.admissibleLabelWeights_of_greenCuspidalParametrisation
    (D : D7) (jE : D.host.E →+* AlgebraicClosure ℚ)
    (T : NormalizedTypesCompatibility D jE) : admLq D := by
  apply admissibleLabelWeights_of_relabelled_series D
  intro k
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨σ, π, hσ, hχ⟩ := exists_cuspidalLabel_permutation (T.O k) (T.labelDatum k)
  refine ⟨T.labelDatum k, σ, π, hσ, fun f hf => ?_⟩
  rw [T.eSer_def, eSerO_eq_eSerC (T.O k) (T.labelDatum k) hχ (five_le_typePrime D k) hσ hf.1 hf.2.2]

end GlobalTheory.GLq
