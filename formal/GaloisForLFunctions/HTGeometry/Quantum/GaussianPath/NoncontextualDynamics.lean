import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.OnsiteOperatorDistance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathMicroscopicCircuitOrder

/-!
# Projective separation from noncontextual path dynamics

The trace removes the scalar part of a comparison between two evolutions.
A first-order estimate then turns a generator gap into a projective
operator gap on a time scale set by the larger generator norm.
-/

open Matrix Filter MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section MatrixEvolution

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

local instance : CStarAlgebra (Matrix d d ℂ) where

omit [Nonempty d] in
private theorem norm_trace_le_card_mul_norm (X : Matrix d d ℂ) :
    ‖X.trace‖ ≤ (Fintype.card d : ℝ) * ‖X‖ := by
  rw [Matrix.trace]
  exact (norm_sum_le _ _).trans (by
    calc
      _ ≤ ∑ _ : d, ‖X‖ := Finset.sum_le_sum fun i _ => norm_entry_le_l2_opNorm X i i
      _ = _ := by simp)

/-- A scalar shift can reduce the operator norm of a traceless matrix by at most half. -/
theorem norm_traceless_le_two_mul_norm_scalar_add (X : Matrix d d ℂ) (hX : X.trace = 0)
    (z : ℂ) : ‖X‖ ≤ 2 * ‖z • (1 : Matrix d d ℂ) + X‖ := by
  let Y := z • (1 : Matrix d d ℂ) + X
  have htrace : Y.trace = z * (Fintype.card d : ℂ) := by
    simp only [Y, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hX, smul_eq_mul, add_zero]
  have hz : ‖z‖ ≤ ‖Y‖ := by
    have h := norm_trace_le_card_mul_norm Y
    rw [htrace, norm_mul, Complex.norm_natCast, mul_comm ‖z‖] at h
    exact le_of_mul_le_mul_left h (Nat.cast_pos.mpr Fintype.card_pos)
  have he : X = Y - z • (1 : Matrix d d ℂ) := by simp [Y]
  calc
    ‖X‖ = ‖Y - z • (1 : Matrix d d ℂ)‖ := congrArg norm he
    _ ≤ ‖Y‖ + ‖z • (1 : Matrix d d ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖Y‖ := by rw [norm_smul, norm_one, mul_one, two_mul]; exact add_le_add le_rfl hz

private def evolutionLinearTerm (H : Matrix d d ℂ) (t : ℝ) : Matrix d d ℂ :=
  ((t : ℂ) * -Complex.I) • H

omit [Nonempty d] in
private theorem norm_evolutionLinearTerm (H : Matrix d d ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖evolutionLinearTerm H t‖ = t * ‖H‖ := by
  rw [evolutionLinearTerm, norm_smul, norm_mul, norm_neg, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg ht]

omit [Nonempty d] in
private theorem norm_unitaryEvolution_sub_linear_le (H : Matrix d d ℂ) (hH : IsSelfAdjoint H)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖unitaryEvolution H t - (1 + evolutionLinearTerm H t)‖ ≤ (t * ‖H‖) ^ 2 / 2 := by
  have h := norm_selfAdjoint_exp_sub_hamiltonianTaylor_le H hH 1 t
  have hTaylor : selfAdjointHamiltonianTaylor H 1 t = 1 + evolutionLinearTerm H t := by
    simp only [selfAdjointHamiltonianTaylor, cstarExponentialTaylor, Finset.sum_range_succ,
      Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, div_one, one_smul, zero_add, evolutionLinearTerm]
    rw [← Complex.real_smul, smul_assoc]
  rw [hTaylor] at h
  change ‖unitaryEvolution H t - (1 + evolutionLinearTerm H t)‖ ≤ _ at h
  simpa [abs_of_nonneg ht, mul_pow, mul_comm] using h

omit [Nonempty d] in
private theorem norm_unitaryEvolution_sub_one_le (H : Matrix d d ℂ) (hH : IsSelfAdjoint H)
    (t : ℝ) (ht : 0 ≤ t) : ‖unitaryEvolution H t - 1‖ ≤ t * ‖H‖ := by
  have hzero : unitaryEvolution H 0 = 1 := by simp [unitaryEvolution]
  simpa only [hzero, sub_zero, abs_of_nonneg ht, mul_comm ‖H‖ t]
    using norm_unitaryEvolution_time_sub_le hH t 0

/-- A first-order generator bound from a phase-adjusted propagator difference.
The quadratic term accounts for both Taylor remainders and the phase correction. -/
theorem projective_unitaryEvolution_linear_estimate (H K : Matrix d d ℂ)
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (htr : (H - K).trace = 0)
    {t M : ℝ} (ht : 0 ≤ t) (hHM : ‖H‖ ≤ M) (hKM : ‖K‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ = 1) :
    t * ‖H - K‖ ≤
      2 * (1 + t * M) * ‖unitaryEvolution H t - z • unitaryEvolution K t‖ + 6 * (t * M) ^ 2 := by
  let δ := t * M
  let L (X : Matrix d d ℂ) := evolutionLinearTerm X t
  let R (X : Matrix d d ℂ) := unitaryEvolution X t - (1 + L X)
  let D := unitaryEvolution H t - z • unitaryEvolution K t
  let W := (1 - z) • (1 : Matrix d d ℂ)
  have hδ : 0 ≤ δ := mul_nonneg ht ((norm_nonneg H).trans hHM)
  have hHδ : t * ‖H‖ ≤ δ := mul_le_mul_of_nonneg_left hHM ht
  have hKδ : t * ‖K‖ ≤ δ := mul_le_mul_of_nonneg_left hKM ht
  have hphase : ‖1 - z‖ ≤ ‖D‖ + 2 * δ := by
    have he : W = (D - (unitaryEvolution H t - 1)) + z • (unitaryEvolution K t - 1) := by
      simp only [W, D, smul_sub, sub_smul, one_smul]
      abel
    have h₁ := norm_sub_le D (unitaryEvolution H t - 1)
    have h₂ := norm_add_le (D - (unitaryEvolution H t - 1)) (z • (unitaryEvolution K t - 1))
    rw [← he] at h₂
    dsimp only [W] at h₂
    rw [norm_smul, norm_one, mul_one, norm_smul, hz, one_mul] at h₂
    linarith only [h₁, h₂, (norm_unitaryEvolution_sub_one_le H hH t ht).trans hHδ,
      (norm_unitaryEvolution_sub_one_le K hK t ht).trans hKδ]
  have hLH : ‖R H‖ ≤ δ ^ 2 / 2 :=
    (norm_unitaryEvolution_sub_linear_le H hH t ht).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg ht (norm_nonneg _)) hHδ 2) (by norm_num))
  have hLK : ‖R K‖ ≤ δ ^ 2 / 2 :=
    (norm_unitaryEvolution_sub_linear_le K hK t ht).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg ht (norm_nonneg _)) hKδ 2) (by norm_num))
  let E := (R H - z • R K) + (1 - z) • L K
  have hE : ‖E‖ ≤ δ ^ 2 + (‖D‖ + 2 * δ) * δ := by
    have h₁ := norm_sub_le (R H) (z • R K)
    rw [norm_smul, hz, one_mul] at h₁
    have h₂ := norm_add_le (R H - z • R K) ((1 - z) • L K)
    have h₃ : ‖(1 - z) • L K‖ ≤ (‖D‖ + 2 * δ) * δ := by
      rw [norm_smul, norm_evolutionLinearTerm K t ht]
      exact mul_le_mul hphase hKδ (mul_nonneg ht (norm_nonneg _)) (by positivity)
    linarith only [h₁, h₂, h₃, hLH, hLK]
  have hw : W + L (H - K) = D - E := by
    simp only [W, L, evolutionLinearTerm, D, E, R, smul_sub, smul_add, sub_smul, one_smul]
    abel
  have hLtrace : (L (H - K)).trace = 0 := by simp [L, evolutionLinearTerm, htr]
  have h := norm_traceless_le_two_mul_norm_scalar_add (L (H - K)) hLtrace (1 - z)
  change ‖L (H - K)‖ ≤ 2 * ‖W + L (H - K)‖ at h
  rw [hw, norm_evolutionLinearTerm (H - K) t ht] at h
  calc
    t * ‖H - K‖ ≤ 2 * (‖D‖ + ‖E‖) :=
      h.trans (mul_le_mul_of_nonneg_left (norm_sub_le D E) (by norm_num))
    _ ≤ 2 * (‖D‖ + (δ ^ 2 + (‖D‖ + 2 * δ) * δ)) := by gcongr
    _ = _ := by change _ = 2 * (1 + δ) * ‖D‖ + 6 * δ ^ 2; ring

/-- The linear term controls the projective distance while time times the
larger generator norm is sufficiently small relative to the normalized gap. -/
theorem projective_unitaryEvolution_dist_ge_of_small_time (H K : Matrix d d ℂ)
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (htr : (H - K).trace = 0)
    {t M q : ℝ} (ht : 0 ≤ t) (hHM : ‖H‖ ≤ M) (hKM : ‖K‖ ≤ M)
    (hq : q ≤ 1) (hgap : q * M ≤ ‖H - K‖) (hstep : t * M ≤ q / 12)
    (z : ℂ) (hz : ‖z‖ = 1) :
    t * ‖H - K‖ / 8 ≤ ‖unitaryEvolution H t - z • unitaryEvolution K t‖ := by
  let δ := t * M
  let D := ‖unitaryEvolution H t - z • unitaryEvolution K t‖
  have hδ : 0 ≤ δ := mul_nonneg ht ((norm_nonneg H).trans hHM)
  have hs : δ ≤ 1 := by linarith only [hstep, hq]
  have hr₁ := mul_le_mul_of_nonneg_left hstep hδ
  have hr₂ := mul_le_mul_of_nonneg_left hgap ht
  have hremainder : 6 * δ ^ 2 ≤ t * ‖H - K‖ / 2 := by
    change δ * δ ≤ δ * (q / 12) at hr₁
    calc
      6 * δ ^ 2 ≤ δ * q / 2 := by nlinarith only [hr₁]
      _ = t * (q * M) / 2 := by dsimp [δ]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hr₂ (by norm_num)
  have hcoeff : 2 * (1 + δ) * D ≤ 4 * D := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    linarith only [hs]
  have h := projective_unitaryEvolution_linear_estimate H K hH hK htr ht hHM hKM z hz
  change t * ‖H - K‖ ≤ 2 * (1 + δ) * D + 6 * δ ^ 2 at h
  change t * ‖H - K‖ / 8 ≤ D
  linarith only [h, hcoeff, hremainder]

private theorem exists_short_time_for_norm_gaps {g M c C N : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hN : 0 < N)
    (hgap : c * N ≤ g) (hMgap : g ≤ 2 * M) (hMnorm : M ≤ C * N + g) :
    let q := c / (c + C)
    ∃ t : ℝ, 0 < t ∧ t ≤ (1 / c) / N ∧
      t * M ≤ q / 12 ∧ q * M ≤ g ∧ q ^ 2 / 12 ≤ t * g := by
  have hMpos : 0 < M := by linarith only [mul_pos hc hN, hgap, hMgap]
  let q := c / (c + C)
  have hqpos : 0 < q := div_pos hc (add_pos hc hC)
  have hq : q ≤ 1 := (div_le_iff₀ (add_pos hc hC)).mpr (by linarith only [hC])
  have hqgap : q * M ≤ g := by
    calc
      q * M = (c * M) / (c + C) := by dsimp [q]; ring
      _ ≤ _ := (div_le_iff₀ (add_pos hc hC)).mpr (by
        calc
          c * M ≤ c * (C * N + g) := mul_le_mul_of_nonneg_left hMnorm hc.le
          _ = C * (c * N) + c * g := by ring
          _ ≤ C * g + c * g := add_le_add (mul_le_mul_of_nonneg_left hgap hC.le) le_rfl
          _ = _ := by ring)
  let t := (q / 12) / M
  have ht : 0 < t := div_pos (div_pos hqpos (by norm_num)) hMpos
  have htM : t * M = q / 12 := div_mul_cancel₀ _ hMpos.ne'
  have htbound : t ≤ (1 / c) / N := by
    have h := mul_le_mul_of_nonneg_left (hgap.trans hMgap) ht.le
    have he : t * (2 * M) = q / 6 := by
      calc
        _ = 2 * (t * M) := by ring
        _ = _ := by rw [htM]; ring
    rw [he] at h
    apply (le_div_iff₀ hN).mpr
    apply (le_div_iff₀ hc).mpr
    calc
      t * N * c = t * (c * N) := by ring
      _ ≤ q / 6 := h
      _ ≤ 1 := by linarith only [hq]
  refine ⟨t, ht, htbound, htM.le, hqgap, ?_⟩
  calc
    q ^ 2 / 12 = q * (t * M) := by rw [htM]; ring
    _ = t * (q * M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hqgap ht.le

/-- A generator gap gives a time of projective separation even if the second
generator has arbitrarily large norm. The observation time is shortened
using the larger of the two norms. -/
theorem exists_time_projective_unitaryEvolution_separation (H K : Matrix d d ℂ)
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (htr : (H - K).trace = 0)
    {c C N : ℝ} (hc : 0 < c) (hC : 0 < C) (hN : 0 < N)
    (hHnorm : ‖H‖ ≤ C * N) (hgap : c * N ≤ ‖H - K‖) :
    ∃ t : ℝ, 0 < t ∧ t ≤ (1 / c) / N ∧ ∀ z : ℂ, ‖z‖ = 1 →
      (c / (c + C)) ^ 2 / 96 ≤ ‖unitaryEvolution H t - z • unitaryEvolution K t‖ := by
  let M := max ‖H‖ ‖K‖
  have hHM : ‖H‖ ≤ M := le_max_left _ _
  have hKM : ‖K‖ ≤ M := le_max_right _ _
  have hMgap : ‖H - K‖ ≤ 2 * M :=
    (norm_sub_le H K).trans (by rw [two_mul]; exact add_le_add hHM hKM)
  have hKnorm : ‖K‖ ≤ ‖H‖ + ‖H - K‖ := by
    calc
      ‖K‖ = ‖H - (H - K)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  have hMnorm : M ≤ C * N + ‖H - K‖ := max_le
    (hHnorm.trans (le_add_of_nonneg_right (norm_nonneg _)))
    (hKnorm.trans (add_le_add hHnorm le_rfl))
  let q := c / (c + C)
  have hq : q ≤ 1 := (div_le_iff₀ (add_pos hc hC)).mpr (by linarith only [hC])
  obtain ⟨t, ht, htbound, htM, hqgap, hlower⟩ := exists_short_time_for_norm_gaps hc hC hN hgap hMgap hMnorm
  refine ⟨t, ht, htbound, fun z hz => ?_⟩
  have hstep := projective_unitaryEvolution_dist_ge_of_small_time
    H K hH hK htr ht.le hHM hKM hq hqgap htM z hz
  change q ^ 2 / 96 ≤ _
  exact (show q ^ 2 / 96 ≤ t * ‖H - K‖ / 8 by linarith only [hlower]).trans hstep

end MatrixEvolution

/-- A path Hamiltonian is traceless because every active word has nonempty support. -/
theorem trace_pathHamiltonian_zero {n : ℕ} (u : PathShell n) : (pathHamiltonian u).trace = 0 := by
  rw [pathHamiltonian_eq_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.trace_smul, finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity l),
    smul_zero]

/-- The Gaussian path Hamiltonian has an eventual linear operator-norm bound. -/
theorem gaussian_ae_pathHamiltonian_linear_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ‖pathHamiltonian (pathPauliDisorderShell ω n)‖ ≤ C * ((n + 2 : ℕ) : ℝ) := by
  obtain ⟨_, b, _, hb, hmass⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨12 + b, by positivity, ?_⟩
  filter_upwards [hmass] with ω hω
  filter_upwards [hω] with n hn
  let u := pathPauliDisorderShell ω n
  calc
    ‖pathHamiltonian u‖ ≤ ∑ l : PathLabel n, |u l| := by
      rw [pathHamiltonian_eq_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_smul, norm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := path_pauli_coefficient_mass_le u b hn.2

/-- Almost surely, every noncontextual path approximation separates from
the Gaussian evolution by a fixed projective error at an inverse-size time
or earlier. The comparison time may depend on the approximant. -/
theorem gaussian_ae_noncontextual_projective_separation :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) →
        ∃ t : ℝ, 0 < t ∧ t ≤ A / ((n + 2 : ℕ) : ℝ) ∧ ∀ z : ℂ, ‖z‖ = 1 →
          ε ≤ ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t -
            z • unitaryEvolution (pathHamiltonian v) t‖ := by
  obtain ⟨C, hC, hUpper⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let c := gaussianOnsiteUnitBoxMass / 2
  have hc : 0 < c := half_pos gaussianOnsiteUnitBoxMass_pos
  have hlt : c < gaussianOnsiteUnitBoxMass := half_lt_self gaussianOnsiteUnitBoxMass_pos
  refine ⟨1 / c, (c / (c + C)) ^ 2 / 96, one_div_pos.mpr hc, by positivity, ?_⟩
  filter_upwards [hUpper, gaussian_ae_eventually_noncontextual_operator_linear_gap] with ω hω hgap
  filter_upwards [hω, hgap c hlt] with n hnorm hsep
  intro v hv
  let u := pathPauliDisorderShell ω n
  refine exists_time_projective_unitaryEvolution_separation (pathHamiltonian u) (pathHamiltonian v)
    (isSelfAdjoint_pathHamiltonian _) (isSelfAdjoint_pathHamiltonian _) ?_
    hc hC (by positivity) hnorm (hsep v hv)
  rw [Matrix.trace_sub, trace_pathHamiltonian_zero, trace_pathHamiltonian_zero, sub_self]

/-- A bound on the approximant's energy per site gives a common inverse-size
time window of projective separation for all such noncontextual evolutions. -/
theorem gaussian_ae_noncontextual_projective_separation_on_window (B : ℝ) (hB : 0 < B) :
    ∃ a ε : ℝ, 0 < a ∧ 0 < ε ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) →
        ‖pathHamiltonian v‖ ≤ B * ((n + 2 : ℕ) : ℝ) →
        ∀ t : ℝ, (a / 2) / ((n + 2 : ℕ) : ℝ) ≤ t → t ≤ a / ((n + 2 : ℕ) : ℝ) →
          ∀ z : ℂ, ‖z‖ = 1 →
            ε ≤ ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t -
              z • unitaryEvolution (pathHamiltonian v) t‖ := by
  obtain ⟨C, hC, hUpper⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let c := gaussianOnsiteUnitBoxMass / 2
  have hc : 0 < c := half_pos gaussianOnsiteUnitBoxMass_pos
  have hlt : c < gaussianOnsiteUnitBoxMass := half_lt_self gaussianOnsiteUnitBoxMass_pos
  let S := C + B
  have hS : 0 < S := add_pos hC hB
  let q := min 1 (c / S)
  have hqpos : 0 < q := lt_min zero_lt_one (div_pos hc hS)
  let a := (q / 12) / S
  have ha : 0 < a := div_pos (div_pos hqpos (by norm_num)) hS
  refine ⟨a, a * c / 16, ha, by positivity, ?_⟩
  filter_upwards [hUpper, gaussian_ae_eventually_noncontextual_operator_linear_gap] with ω hω hgap
  filter_upwards [hω, hgap c hlt] with n hnorm hsep
  let N : ℝ := (n + 2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  intro v hv hV t ht₁ ht₂ z hz
  let H := pathHamiltonian (pathPauliDisorderShell ω n)
  let K := pathHamiltonian v
  let M := S * N
  have hH : ‖H‖ ≤ M := hnorm.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) hN.le)
  have hK : ‖K‖ ≤ M := hV.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hN.le)
  have ht : 0 < t := (div_pos (half_pos ha) hN).trans_le ht₁
  have hq : q ≤ 1 := min_le_left _ _
  have hqM : q * M ≤ ‖H - K‖ := by
    have hqS : q * S ≤ c := (le_div_iff₀ hS).mp (min_le_right _ _)
    calc
      q * M = (q * S) * N := by dsimp [M]; ring
      _ ≤ c * N := mul_le_mul_of_nonneg_right hqS hN.le
      _ ≤ _ := hsep v hv
  have htM : t * M ≤ q / 12 := by
    calc
      t * M = (t * N) * S := by dsimp [M]; ring
      _ ≤ a * S := mul_le_mul_of_nonneg_right ((le_div_iff₀ hN).mp ht₂) hS.le
      _ = _ := div_mul_cancel₀ _ hS.ne'
  have htr : (H - K).trace = 0 := by
    simp only [H, K, Matrix.trace_sub, trace_pathHamiltonian_zero, sub_self]
  have hmain := projective_unitaryEvolution_dist_ge_of_small_time H K
    (isSelfAdjoint_pathHamiltonian _) (isSelfAdjoint_pathHamiltonian _) htr ht.le hH hK hq hqM htM z hz
  have hlower : (a / 2) * c ≤ t * ‖H - K‖ := by
    calc
      (a / 2) * c ≤ (t * N) * c := mul_le_mul_of_nonneg_right ((div_le_iff₀ hN).mp ht₁) hc.le
      _ = t * (c * N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsep v hv) ht.le
  change a * c / 16 ≤ ‖unitaryEvolution H t - z • unitaryEvolution K t‖
  linarith only [hmain, hlower]

#print axioms norm_traceless_le_two_mul_norm_scalar_add
#print axioms projective_unitaryEvolution_linear_estimate
#print axioms projective_unitaryEvolution_dist_ge_of_small_time
#print axioms exists_time_projective_unitaryEvolution_separation
#print axioms trace_pathHamiltonian_zero
#print axioms gaussian_ae_pathHamiltonian_linear_norm_bound
#print axioms gaussian_ae_noncontextual_projective_separation
#print axioms gaussian_ae_noncontextual_projective_separation_on_window

end

end GaloisForLFunctions.HTGeometry
