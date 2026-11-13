import Zeta23.Taper
import Zeta23.Hypotheses.GzGp
import Zeta23.PrimeSideA.Bridge
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The full-line pole compression vanishes

Grid orthogonality and Plancherel give a sharp synthesis bound. The second
spectral moment controls the part outside the height window, where the pole
density is large. Together these estimates make the normalized literal pole
quadratic form uniformly small, including its full-line tails.
-/

open MeasureTheory Complex Real Set Filter Topology
open scoped BigOperators FourierTransform ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem grid_pair_integral {L : ℝ} (hL : 0 < L) (i j : ℤ) :
    (∫ u in -(L / 2)..L / 2,
      fourier i (u : AddCircle L) * conj (fourier j (u : AddCircle L))) =
      if i = j then (L : ℂ) else 0 := by
  letI : Fact (0 < L) := ⟨hL⟩
  have h := congrFun (fourierCoeff_fourier (T := L) i) j
  rw [fourierCoeff_eq_intervalIntegral _ _ (-(L / 2))] at h
  have he : -(L / 2) + L = L / 2 := by ring
  rw [he] at h
  simp only [smul_eq_mul, Complex.real_smul, fourier_neg] at h
  have hp : (∫ u in -(L / 2)..L / 2,
      fourier i (u : AddCircle L) * conj (fourier j (u : AddCircle L))) =
      ∫ u in -(L / 2)..L / 2,
        conj (fourier j (u : AddCircle L)) * fourier i (u : AddCircle L) := by
    congr 1
    funext u
    exact mul_comm _ _
  rw [hp]
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  split_ifs with hij
  · subst j
    simp only [Pi.single_eq_same] at h
    push_cast at h
    field_simp at h
    simpa only [mul_zero] using h
  · have hji : j ≠ i := Ne.symm hij
    simp only [Pi.single_eq_of_ne hji] at h
    push_cast at h
    field_simp at h
    simpa only [mul_zero] using h

private def gridPolynomial {d : ℕ} (L : ℝ) (c : Fin d → ℂ) (u : ℝ) : ℂ :=
  ∑ k, c k * fourier (-(k : ℤ)) (u : AddCircle L)

private theorem gridPolynomial_continuous {d : ℕ} (L : ℝ) (c : Fin d → ℂ) :
    Continuous (gridPolynomial L c) := by
  unfold gridPolynomial
  fun_prop

private theorem gridPolynomial_energy {d : ℕ} {L : ℝ} (hL : 0 < L)
    (c : Fin d → ℂ) :
    (∫ u in -(L / 2)..L / 2, ‖gridPolynomial L c u‖ ^ 2) =
      L * ∑ k, ‖c k‖ ^ 2 := by
  classical
  have hp (u : ℝ) : ((‖gridPolynomial L c u‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * conj (c j) *
        (fourier (-(i : ℤ)) (u : AddCircle L) *
          conj (fourier (-(j : ℤ)) (u : AddCircle L))) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [gridPolynomial, map_sum, map_mul]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hi (i j : Fin d) : IntervalIntegrable (fun u : ℝ => c i * conj (c j) *
      (fourier (-(i : ℤ)) (u : AddCircle L) *
        conj (fourier (-(j : ℤ)) (u : AddCircle L)))) volume (-(L/2)) (L/2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (show Continuous (fun u : ℝ => ∑ j, c i * conj (c j) *
      (fourier (-(i : ℤ)) (u : AddCircle L) *
        conj (fourier (-(j : ℤ)) (u : AddCircle L)))) from by fun_prop).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hi _ j),
    intervalIntegral.integral_const_mul, grid_pair_integral hL]
  have he (i j : Fin d) : (-(i : ℤ) = -(j : ℤ)) ↔ i = j := by
    simp only [neg_inj, Int.natCast_inj, Fin.val_inj]
  simp only [he, mul_ite, mul_zero]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  · intro j _ hji
    rw [if_neg (Ne.symm hji)]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

open Zeta23

/-- A coefficient vector synthesized in the literal sampled Fourier family. -/
def zetaSamplingSynthesis (P : Params) (T : ℝ) {d : ℕ} (c : Fin d → ℂ) (τ : ℝ) : ℂ :=
  ∑ k, c k * (P.phiHatR T (τ - P.tau T k) : ℂ)

private def samplingPacket (P : Params) (T : ℝ) {d : ℕ} (c : Fin d → ℂ) (u : ℝ) : ℂ :=
  (P.phi T u : ℂ) * Complex.exp (-(Complex.I * T * u)) * gridPolynomial (P.L T) c u

private theorem samplingPacket_continuous {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {d : ℕ} (c : Fin d → ℂ) :
    Continuous (samplingPacket P T c) := by
  have hc := Params.phi_continuous hP hwL
  have hg := gridPolynomial_continuous (P.L T) c
  unfold samplingPacket
  fun_prop

private theorem samplingPacket_hasCompactSupport {P : Params} (hP : P.Valid) (T : ℝ)
    {d : ℕ} (c : Fin d → ℂ) : HasCompactSupport (samplingPacket P T c) := by
  exact ((Params.phi_hasCompactSupport hP).comp_left (g := fun x : ℝ => (x : ℂ))
    (by simp)).mul_right.mul_right

private theorem samplingPacket_eq_sum {P : Params} {T : ℝ}
    {d : ℕ} (c : Fin d → ℂ) (u : ℝ) :
    samplingPacket P T c u = ∑ k, c k * P.fk T k u := by
  unfold samplingPacket gridPolynomial
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourier_coe_apply, Params.fk]
  simp only [Int.cast_neg]
  have he : Complex.exp (-(Complex.I * T * u)) *
      Complex.exp (2 * π * Complex.I * (-(k : ℤ)) * u / P.L T) =
        Complex.exp (-(Complex.I * (P.tau T k) * u)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Params.tau, Params.hgrid]
    push_cast
    field_simp
    ring
  calc _ = c k * (P.phi T u : ℂ) *
      (Complex.exp (-(Complex.I * T * u)) *
        Complex.exp (2 * π * Complex.I * (-(k : ℤ)) * u / P.L T)) := by ring
    _ = _ := by rw [he]; ring

private theorem samplingPacket_fourier {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {d : ℕ} (c : Fin d → ℂ) (τ : ℝ) :
    paperFT (samplingPacket P T c) τ = zetaSamplingSynthesis P T c τ := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hf (k : Fin d) : Continuous (P.fk T k) := by
    have hc := Params.phi_continuous hP hwL
    unfold Params.fk
    fun_prop
  have hs (k : Fin d) : HasCompactSupport (P.fk T k) :=
    ((Params.phi_hasCompactSupport hP).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right
  have hi (k : Fin d) : Integrable (fun u : ℝ => c k * P.fk T k u *
      Complex.exp (Complex.I * τ * u)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact (hs k).mul_left.mul_right
  rw [paperFT_def]
  simp_rw [samplingPacket_eq_sum c, Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ => hi k)]
  unfold zetaSamplingSynthesis
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (fun u : ℝ => c k * P.fk T k u * Complex.exp (Complex.I * τ * u)) =
      fun u => c k * (P.fk T k u * Complex.exp (Complex.I * τ * u)) by funext u; ring,
    integral_const_mul_C, ← paperFT_def, GzGp.paperFT_fk,
    ← Complex.ofReal_sub, Params.phiHat_ofReal]

private theorem samplingPacket_norm {P : Params} (hP : P.Valid) (T : ℝ)
    {d : ℕ} (c : Fin d → ℂ) (u : ℝ) :
    ‖samplingPacket P T c u‖ = P.phi T u * ‖gridPolynomial (P.L T) c u‖ := by
  rw [samplingPacket, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Params.phi_nonneg hP u)]
  have he : ‖Complex.exp (-(Complex.I * T * u))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  rw [he, mul_one]

/-- The exact lattice is a Bessel family, with constant `2πL`; the taper is bounded by one. -/
theorem integral_zetaSamplingSynthesis_sq_le {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {d : ℕ} (c : Fin d → ℂ) :
    (∫ τ, ‖zetaSamplingSynthesis P T c τ‖ ^ 2) ≤
      2 * π * P.L T * ∑ k, ‖c k‖ ^ 2 := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hc := samplingPacket_continuous hP hwL c
  have hs := samplingPacket_hasCompactSupport hP T c
  have h1 : Integrable (samplingPacket P T c) := hc.integrable_of_hasCompactSupport hs
  have h2 : MemLp (samplingPacket P T c) 2 := hc.memLp_of_hasCompactSupport hs
  have hpl := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq h1 h2
  have hd : (fun τ : ℝ => ‖paperFT (samplingPacket P T c) τ‖ ^ 2) =
      fun τ : ℝ => (fun ξ : ℝ => ‖𝓕 (samplingPacket P T c) ξ‖ ^ 2)
        (τ / (-(2 * π))) := by
    funext τ
    rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
  have hpl' : (∫ τ : ℝ, ‖paperFT (samplingPacket P T c) τ‖ ^ 2) =
      2 * π * ∫ u, ‖samplingPacket P T c u‖ ^ 2 := by
    rw [hd, Measure.integral_comp_div
      (fun ξ : ℝ => ‖𝓕 (samplingPacket P T c) ξ‖ ^ 2) (-(2 * π)),
      hpl, abs_neg, abs_of_pos (by positivity),
      smul_eq_mul]
  have hb : (∫ u, ‖samplingPacket P T c u‖ ^ 2) ≤
      P.L T * ∑ k, ‖c k‖ ^ 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-(P.L T/2)) (P.L T/2))
      (fun u hu => ?_)]
    · calc (∫ u in Icc (-(P.L T/2)) (P.L T/2), ‖samplingPacket P T c u‖ ^ 2)
          ≤ ∫ u in Icc (-(P.L T/2)) (P.L T/2), ‖gridPolynomial (P.L T) c u‖ ^ 2 := by
            apply integral_mono (hc.norm.pow 2).integrableOn_Icc
              ((gridPolynomial_continuous (P.L T) c).norm.pow 2).integrableOn_Icc
            intro u
            change ‖samplingPacket P T c u‖ ^ 2 ≤ ‖gridPolynomial (P.L T) c u‖ ^ 2
            rw [samplingPacket_norm hP]
            apply pow_le_pow_left₀ (mul_nonneg (Params.phi_nonneg hP u) (norm_nonneg _))
            exact mul_le_of_le_one_left (norm_nonneg _) (Params.phi_le_one hP u)
        _ = P.L T * ∑ k, ‖c k‖ ^ 2 := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
          exact gridPolynomial_energy hL c
    · have hu' : P.L T/2 ≤ |u| := by
        by_contra hn
        apply hu
        have := abs_lt.mp (lt_of_not_ge hn)
        exact ⟨this.1.le, this.2.le⟩
      rw [samplingPacket, Params.phi_eq_zero hP hu']
      simp
  simp_rw [samplingPacket_fourier hP hwL c] at hpl'
  rw [hpl']
  nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * π by positivity)]

/-- The actual Fourier taper has a uniform quadratic-moment tail. -/
theorem integral_phiHatR_sq_tail_le {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {R : ℝ} (hR : 0 < R) :
    (∫ r in {r : ℝ | R ≤ |r|}, P.phiHatR T r ^ 2) ≤
      (8 + 2 * (P.crho / P.w) ^ 2) / R ^ 2 := by
  have hs : MeasurableSet {r : ℝ | R ≤ |r|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hi := Params.integrable_phiHatR_sq hP hwL
  have hj := Params.integrable_phiHatR_sq_mul_sq hP hwL
  calc (∫ r in {r : ℝ | R ≤ |r|}, P.phiHatR T r ^ 2)
      ≤ ∫ r in {r : ℝ | R ≤ |r|},
          P.phiHatR T r ^ 2 * r ^ 2 / R ^ 2 := by
        apply integral_mono_ae hi.integrableOn (hj.div_const _).integrableOn
        filter_upwards [ae_restrict_mem hs] with r hr
        rw [le_div_iff₀ (sq_pos_of_pos hR)]
        have hr2 : R ^ 2 ≤ r ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ hR.le hr 2
        exact mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)
    _ = (∫ r in {r : ℝ | R ≤ |r|}, P.phiHatR T r ^ 2 * r ^ 2) / R ^ 2 :=
      integral_div _ _
    _ ≤ (∫ r, P.phiHatR T r ^ 2 * r ^ 2) / R ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact setIntegral_le_integral hj (Filter.Eventually.of_forall fun r => by positivity)
    _ ≤ (8 + 2 * (P.crho / P.w) ^ 2) / R ^ 2 := by
      exact div_le_div_of_nonneg_right (Params.integral_phiHatR_sq_mul_sq_le hP hwL)
        (sq_nonneg _)

/-- The full-line sampling tail includes the neighborhood of the pole at zero. -/
theorem integral_phiHatR_sq_outside_le {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc T (2*T)) :
    (∫ τ in (Icc (T/2) (3*T))ᶜ, P.phiHatR T (τ-t) ^ 2) ≤
      4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2 := by
  have hi := (Params.integrable_phiHatR_sq hP hwL).comp_sub_right t
  have hj := (Params.integrable_phiHatR_sq_mul_sq hP hwL).comp_sub_right t
  have hdist {τ : ℝ} (hτ : τ ∈ (Icc (T/2) (3*T))ᶜ) : T ^ 2 ≤ 4 * (τ-t) ^ 2 := by
    have hτ' : τ < T/2 ∨ 3*T < τ := by
      simpa only [mem_compl_iff, mem_Icc, not_and_or, not_le] using hτ
    rcases hτ' with hτ' | hτ'
    · have h : T/2 ≤ |τ-t| := by
        rw [abs_of_nonpos (by linarith [ht.1])]
        linarith [ht.1]
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ T/2) h 2
      rw [sq_abs] at hh
      nlinarith only [hh]
    · have h : T/2 ≤ |τ-t| := by
        rw [abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.2]
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ T/2) h 2
      rw [sq_abs] at hh
      nlinarith only [hh]
  calc (∫ τ in (Icc (T/2) (3*T))ᶜ, P.phiHatR T (τ-t) ^ 2)
      ≤ ∫ τ in (Icc (T/2) (3*T))ᶜ,
          4 * (P.phiHatR T (τ-t) ^ 2 * (τ-t) ^ 2) / T ^ 2 := by
        apply integral_mono_ae hi.integrableOn ((hj.const_mul 4).div_const _).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with τ hτ
        rw [le_div_iff₀ (sq_pos_of_pos hT)]
        have hh := mul_le_mul_of_nonneg_left (hdist hτ) (sq_nonneg (P.phiHatR T (τ-t)))
        nlinarith only [hh]
    _ = 4 * (∫ τ in (Icc (T/2) (3*T))ᶜ,
        P.phiHatR T (τ-t) ^ 2 * (τ-t) ^ 2) / T ^ 2 := by
      rw [integral_div, integral_const_mul]
    _ ≤ 4 * (∫ τ, P.phiHatR T (τ-t) ^ 2 * (τ-t) ^ 2) / T ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hj (Filter.Eventually.of_forall fun τ => by positivity)) (by norm_num)
    _ = 4 * (∫ r, P.phiHatR T r ^ 2 * r ^ 2) / T ^ 2 := by
      rw [integral_sub_right_eq_self (fun r => P.phiHatR T r ^ 2 * r ^ 2) t]
    _ ≤ 4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2 := by
      gcongr
      exact Params.integral_phiHatR_sq_mul_sq_le hP hwL

/-- Pointwise Cauchy–Schwarz for the literal sampled Fourier family. -/
theorem zetaSamplingSynthesis_sq_le (P : Params) (T : ℝ) {d : ℕ} (c : Fin d → ℂ) (τ : ℝ) :
    ‖zetaSamplingSynthesis P T c τ‖ ^ 2 ≤
      (∑ k, ‖c k‖ ^ 2) * ∑ k : Fin d, P.phiHatR T (τ-P.tau T k) ^ 2 := by
  classical
  have ht : ‖zetaSamplingSynthesis P T c τ‖ ≤
      ∑ k, ‖c k‖ * |P.phiHatR T (τ-P.tau T k)| := by
    unfold zetaSamplingSynthesis
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      (norm_sum_le (s := Finset.univ) (f := fun k => c k *
        (P.phiHatR T (τ-P.tau T k) : ℂ)))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => ‖c k‖) (fun k => |P.phiHatR T (τ-P.tau T k)|)
  simp only [sq_abs] at hc
  exact hsq.trans hc

theorem integrable_zetaSamplingSynthesis_sq {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {d : ℕ} (c : Fin d → ℂ) :
    Integrable (fun τ => ‖zetaSamplingSynthesis P T c τ‖ ^ 2) := by
  have hf (k : Fin d) := (Params.integrable_phiHatR_sq hP hwL).comp_sub_right (P.tau T k)
  have hi := (integrable_finsetSum Finset.univ (fun k _ => hf k)).const_mul (∑ k, ‖c k‖ ^ 2)
  have hc : Continuous (zetaSamplingSynthesis P T c) := by
    have hh := Params.phiHatR_continuous hP hwL
    unfold zetaSamplingSynthesis
    fun_prop
  apply hi.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards with τ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact zetaSamplingSynthesis_sq_le P T c τ

/-- The entire sampled space has only `O(d/T²)` mass outside the enlarged height window. -/
theorem integral_zetaSamplingSynthesis_sq_outside_le {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) (hT : 0 < T) (c : Fin (P.d T) → ℂ) :
    (∫ τ in (Icc (T/2) (3*T))ᶜ, ‖zetaSamplingSynthesis P T c τ‖ ^ 2) ≤
      (∑ k, ‖c k‖ ^ 2) * (P.d T) *
        (4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hf (k : Fin (P.d T)) :=
    (Params.integrable_phiHatR_sq hP hwL).comp_sub_right (P.tau T k)
  have ht (k : Fin (P.d T)) : P.tau T k ∈ Icc T (2*T) := by
    exact (P.toSetting T).tau_mem hL hT.le (Finset.mem_range.mpr k.isLt)
  calc (∫ τ in (Icc (T/2) (3*T))ᶜ, ‖zetaSamplingSynthesis P T c τ‖ ^ 2)
      ≤ ∫ τ in (Icc (T/2) (3*T))ᶜ,
        (∑ k, ‖c k‖ ^ 2) * ∑ k : Fin (P.d T), P.phiHatR T (τ-P.tau T k) ^ 2 := by
        apply integral_mono (integrable_zetaSamplingSynthesis_sq hP hwL c).integrableOn
          ((integrable_finsetSum Finset.univ (fun k _ => hf k)).const_mul _).integrableOn
        exact zetaSamplingSynthesis_sq_le P T c
    _ = (∑ k, ‖c k‖ ^ 2) * ∑ k : Fin (P.d T),
        ∫ τ in (Icc (T/2) (3*T))ᶜ, P.phiHatR T (τ-P.tau T k) ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _ (fun k _ => (hf k).integrableOn)]
    _ ≤ (∑ k, ‖c k‖ ^ 2) * ∑ k : Fin (P.d T),
        4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun k _ => integral_phiHatR_sq_outside_le hP hwL hT (ht k)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

/-- Every coefficient vector obeys the full-line pole bound; the pole near zero is covered
by the exterior sampling tail. -/
theorem abs_integral_pole_sampling_sq_le {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) (hT : 0 < T) (c : Fin (P.d T) → ℂ) :
    |∫ τ, PiX (P.X T) τ * ‖zetaSamplingSynthesis P T c τ‖ ^ 2| ≤
      ((6 * Real.sqrt (P.X T) / T) * (2 * π * P.L T) +
        3 * Real.sqrt (P.X T) * (P.d T) *
          (4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2)) * ∑ k, ‖c k‖ ^ 2 := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hX : 1 ≤ P.X T := Real.one_le_exp hL.le
  let J : Set ℝ := Icc (T/2) (3*T)
  have hJ : MeasurableSet J := measurableSet_Icc
  let E : ℝ → ℝ := fun τ => ‖zetaSamplingSynthesis P T c τ‖ ^ 2
  have hi : Integrable E := integrable_zetaSamplingSynthesis_sq hP hwL c
  have hm : Integrable (fun τ => (6 * Real.sqrt (P.X T) / T) * E τ +
      3 * Real.sqrt (P.X T) * Jᶜ.indicator E τ) :=
    (hi.const_mul _).add ((hi.indicator hJ.compl).const_mul _)
  have hp (τ : ℝ) : |PiX (P.X T) τ| ≤ 3 * Real.sqrt (P.X T) :=
    (PiX_abs_le hX τ).trans (div_le_self (by positivity) (by linarith [abs_nonneg τ]))
  have hpJ {τ : ℝ} (hτ : τ ∈ J) : |PiX (P.X T) τ| ≤ 6 * Real.sqrt (P.X T) / T := by
    have hτ0 : 0 ≤ τ := by have := hτ.1; linarith
    apply (PiX_abs_le hX τ).trans
    rw [div_le_div_iff₀ (by positivity) hT, abs_of_nonneg hτ0]
    have htau := hτ.1
    have hb := mul_le_mul_of_nonneg_left htau
      (show 0 ≤ 6 * Real.sqrt (P.X T) by positivity)
    nlinarith only [hb, Real.sqrt_nonneg (P.X T)]
  have hb : |∫ τ, PiX (P.X T) τ * E τ| ≤
      (6 * Real.sqrt (P.X T) / T) * (∫ τ, E τ) +
        3 * Real.sqrt (P.X T) * (∫ τ in Jᶜ, E τ) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ τ, PiX (P.X T) τ * E τ‖
        ≤ ∫ τ, (6 * Real.sqrt (P.X T) / T) * E τ +
            3 * Real.sqrt (P.X T) * Jᶜ.indicator E τ := by
          apply norm_integral_le_of_norm_le hm
          filter_upwards with τ
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ E τ from sq_nonneg _)]
          by_cases hτ : τ ∈ J
          · rw [Set.indicator_of_notMem (by simpa using hτ)]
            simp only [mul_zero, add_zero]
            exact mul_le_mul_of_nonneg_right (hpJ hτ) (sq_nonneg _)
          · rw [Set.indicator_of_mem (show τ ∈ Jᶜ from hτ)]
            have he : 0 ≤ E τ := sq_nonneg _
            have hn : 0 ≤ (6 * Real.sqrt (P.X T) / T) * E τ := by positivity
            exact (mul_le_mul_of_nonneg_right (hp τ) he).trans (by linarith only [hn])
      _ = _ := by
        rw [integral_add (hi.const_mul _) ((hi.indicator hJ.compl).const_mul _),
          integral_const_mul, integral_const_mul, integral_indicator hJ.compl]
  have hmain := integral_zetaSamplingSynthesis_sq_le hP hwL c
  have htail := integral_zetaSamplingSynthesis_sq_outside_le hP hwL hT c
  calc |∫ τ, PiX (P.X T) τ * E τ| ≤ _ := hb
    _ ≤ (6 * Real.sqrt (P.X T) / T) *
          (2 * π * P.L T * ∑ k, ‖c k‖ ^ 2) +
        3 * Real.sqrt (P.X T) * ((∑ k, ‖c k‖ ^ 2) * (P.d T) *
          (4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2)) := by
      simpa only [E, J] using
        add_le_add (mul_le_mul_of_nonneg_left hmain
          (show 0 ≤ 6 * Real.sqrt (P.X T) / T by positivity))
          (mul_le_mul_of_nonneg_left htail (show 0 ≤ 3 * Real.sqrt (P.X T) by positivity))
    _ = _ := by ring

/-- The quadratic form of the normalized literal pole compression. -/
def normalizedPoleQuadratic (P : Params) (T : ℝ) (c : Fin (P.d T) → ℂ) : ℝ :=
  (∫ τ, PiX (P.X T) τ * ‖zetaSamplingSynthesis P T c τ‖ ^ 2) / (P.a T * P.L T ^ 2)

/-- Normalization preserves the full-line estimate without a fourth-moment input. -/
theorem abs_normalizedPoleQuadratic_le {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) (hT : 0 < T) (c : Fin (P.d T) → ℂ) :
    |normalizedPoleQuadratic P T c| ≤
      ((6 * Real.sqrt (P.X T) / T) * (2 * π * P.L T) +
        3 * Real.sqrt (P.X T) * (P.d T) *
          (4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2)) /
        (P.a T * P.L T ^ 2) * ∑ k, ‖c k‖ ^ 2 := by
  have ha : 0 < P.a T := by
    have hb := Params.three_quarters_le_b hP hwL
    have hba := Params.b_le_a hP hwL
    linarith only [hb, hba]
  rw [normalizedPoleQuadratic, abs_div, abs_of_pos (mul_pos ha (sq_pos_of_pos
    (by linarith [hP.one_le_w] : 0 < P.L T)))]
  calc _ ≤ (((6 * Real.sqrt (P.X T) / T) * (2 * π * P.L T) +
      3 * Real.sqrt (P.X T) * (P.d T) *
        (4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2)) * ∑ k, ‖c k‖ ^ 2) /
          (P.a T * P.L T ^ 2) :=
      div_le_div_of_nonneg_right (abs_integral_pole_sampling_sq_le hP hwL hT c) (by positivity)
    _ = _ := by ring

/-- A constant determined only by the fixed taper. -/
def poleCompressionConstant (P : Params) : ℝ :=
  12 * π + 6 * (8 + 2 * (P.crho / P.w) ^ 2) / π

theorem poleCompressionConstant_pos (P : Params) : 0 < poleCompressionConstant P := by
  unfold poleCompressionConstant
  positivity

/-- The dimension bound reduces the normalized full-line pole estimate to `O(√X/(LT))`. -/
theorem abs_normalizedPoleQuadratic_le_sqrt_div {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) (hT : 0 < T) (c : Fin (P.d T) → ℂ) :
    |normalizedPoleQuadratic P T c| ≤
      poleCompressionConstant P * Real.sqrt (P.X T) / (P.a T * P.L T * T) *
        ∑ k, ‖c k‖ ^ 2 := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have ha : 0 < P.a T := by
    have hb := Params.three_quarters_le_b hP hwL
    have hba := Params.b_le_a hP hwL
    linarith only [hb, hba]
  have hd : (P.d T : ℝ) ≤ P.L T * T / (2 * π) :=
    (P.toSetting T).d_le (mul_nonneg hL.le hT.le)
  refine (abs_normalizedPoleQuadratic_le hP hwL hT c).trans ?_
  calc
    _ ≤ ((6 * Real.sqrt (P.X T) / T) * (2 * π * P.L T) +
        3 * Real.sqrt (P.X T) * (P.L T * T / (2 * π)) *
          (4 * (8 + 2 * (P.crho / P.w) ^ 2) / T ^ 2)) /
        (P.a T * P.L T ^ 2) * ∑ k, ‖c k‖ ^ 2 := by
      gcongr
    _ = _ := by
      unfold poleCompressionConstant
      field_simp
      ring

private theorem X_le_height {P : Params} (hP : P.Valid) {T : ℝ} (hT : 2 * π ≤ T) :
    P.X T ≤ T := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hratio : 1 ≤ T / (2 * π) := (le_div_iff₀ (by positivity)).mpr (by simpa using hT)
  have hl : 0 ≤ l T := Real.log_nonneg hratio
  calc P.X T = Real.exp (P.lam * l T) := rfl
    _ ≤ Real.exp (l T) := Real.exp_le_exp.mpr (mul_le_of_le_one_left hl hP.lam_le_one)
    _ = T / (2 * π) := Real.exp_log (by positivity)
    _ ≤ T := div_le_self hT0.le (by linarith [Real.pi_gt_three])

/-- The normalized pole compression tends uniformly to zero on unit coefficient vectors. -/
theorem normalizedPoleQuadratic_uniformly_small {P : Params} (hP : P.Valid) {ε : ℝ}
    (hε : 0 < ε) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ c : Fin (P.d T) → ℂ,
      |normalizedPoleQuadratic P T c| ≤ ε * ∑ k, ‖c k‖ ^ 2 := by
  have hlim : Filter.Tendsto (fun T : ℝ => poleCompressionConstant P / 6 * (Real.sqrt T)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul
      (poleCompressionConstant P / 6)
  obtain ⟨T₁, hT₁⟩ := PrimeSide.localHypsEventually hP
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨max T₁ (max T₂ (2 * π)), fun T hT c => ?_⟩
  have ht₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have ht₂ : T₂ ≤ T := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hT
  have htπ : 2 * π ≤ T := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) htπ
  have hwL : 8 * P.w ≤ P.L T := by
    have hw := (hT₁ T ht₁).w_le
    change P.w ≤ P.L T / 8 at hw
    linarith only [hw]
  have ha : 3 / 4 ≤ P.a T :=
    (Params.three_quarters_le_b hP hwL).trans (Params.b_le_a hP hwL)
  have hL : 8 ≤ P.L T := by linarith [hP.one_le_w]
  have hAL : 6 ≤ P.a T * P.L T := by
    have hh := mul_le_mul ha hL (by norm_num : (0 : ℝ) ≤ 8) (by linarith : 0 ≤ P.a T)
    norm_num at hh
    exact hh
  have hcoeff : poleCompressionConstant P * Real.sqrt (P.X T) / (P.a T * P.L T * T) ≤
      poleCompressionConstant P / 6 * (Real.sqrt T)⁻¹ := by
    have hK : 0 ≤ poleCompressionConstant P := (poleCompressionConstant_pos P).le
    calc
      _ ≤ poleCompressionConstant P * Real.sqrt T / (P.a T * P.L T * T) := by
        gcongr
        exact X_le_height hP htπ
      _ ≤ poleCompressionConstant P * Real.sqrt T / (6 * T) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hAL hT0.le
      _ = _ := by
        have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
        have hs2 := Real.sq_sqrt hT0.le
        field_simp
        rw [hs2]
  refine (abs_normalizedPoleQuadratic_le_sqrt_div hP hwL hT0 c).trans ?_
  exact mul_le_mul_of_nonneg_right (hcoeff.trans (hT₂ T ht₂).le) (by positivity)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.integral_zetaSamplingSynthesis_sq_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.abs_normalizedPoleQuadratic_le_sqrt_div
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.normalizedPoleQuadratic_uniformly_small
