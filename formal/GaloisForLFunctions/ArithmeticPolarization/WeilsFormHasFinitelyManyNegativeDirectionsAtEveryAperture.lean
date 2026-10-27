import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormSamplesHighFrequencies

/-!
# Weil's form has finitely many negative directions at every aperture

**Theorem** (`card_negative_orthonormal_le`). For every aperture `A > 0` there is a bound `B` such
that every family `e_1, …, e_n` of `C²` tests supported in `[−A, A]`, orthonormal in `L²`, with
`Re W(e_j, e_j) < 0` for every `j`, has `n < B`. Explicitly `B = 2AT₀K/π` with the constants of the
Gårding inequality (`re_W_ge_sub_lowMass`). In particular every subspace of such tests on which
Weil's form is negative definite has dimension `< B`: unconditionally, positivity of Weil's form
fails at each aperture in at most finitely many orthogonal directions.

**Proof.** By Gårding, `Re W(e_j) < 0` forces the low-frequency mass `∫_{−T₀}^{T₀} |ê_j|²` above
`2π/K`. By Bessel's inequality for the exponential `u ↦ e^{−iτu}` on `[−A, A]`
(`sum_norm_sq_paperFT_le`), `Σ_j |ê_j(τ)|² ≤ 2A` at every frequency, so the total low-frequency
mass is at most `4AT₀`.
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- The core of Bessel: `‖h − g‖² ≥ 0` with `⟨g, h⟩ = ⟨g, g⟩ = S` gives `S ≤ ‖h‖²`. -/
theorem bessel_core {h g : ℝ → ℂ} {S : ℝ} (hh2 : Integrable fun u => ‖h u‖ ^ 2)
    (hgh_int : Integrable fun u => g u * conj (h u)) (hgg_int : Integrable fun u => g u * conj (g u))
    (hgc : Continuous g) (hgcs : HasCompactSupport g)
    (hgh : ∫ u, g u * conj (h u) = S) (hgg : ∫ u, g u * conj (g u) = S) :
    S ≤ ∫ u, ‖h u‖ ^ 2 := by
  have hgg_re : ∫ u, ‖g u‖ ^ 2 = S := by
    have : (fun u => ‖g u‖ ^ 2) = fun u => (g u * conj (g u)).re := by
      funext u; rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [this, show (∫ u, (g u * conj (g u)).re) = (∫ u, g u * conj (g u)).re from
      (integral_re hgg_int), hgg, Complex.ofReal_re]
  have hgh_re : ∫ u, (g u * conj (h u)).re = S := by
    rw [show (∫ u, (g u * conj (h u)).re) = (∫ u, g u * conj (h u)).re from
      (integral_re hgh_int), hgh, Complex.ofReal_re]
  have hgint : Integrable fun u => ‖g u‖ ^ 2 :=
    (hgc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro hgcs fun u hu => by
      show ‖g u‖ ^ 2 = 0
      rw [image_eq_zero_of_notMem_tsupport hu, norm_zero]; norm_num)
  have hpt : ∀ u, ‖h u - g u‖ ^ 2 = ‖h u‖ ^ 2 - 2 * (g u * conj (h u)).re + ‖g u‖ ^ 2 := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
    have : (h u * conj (g u)).re = (g u * conj (h u)).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    rw [this]; ring
  have hre_int : Integrable fun u => (g u * conj (h u)).re := hgh_int.re
  have h1 : Integrable fun u => ‖h u‖ ^ 2 - 2 * (g u * conj (h u)).re := hh2.sub (hre_int.const_mul 2)
  have hexpand : ∫ u, ‖h u - g u‖ ^ 2 = (∫ u, ‖h u‖ ^ 2) - S := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add h1 hgint,
      integral_sub hh2 (hre_int.const_mul 2), integral_const_mul, hgh_re, hgg_re]
    ring
  have hnonneg : 0 ≤ ∫ u, ‖h u - g u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [hexpand] at hnonneg
  linarith

/-- Pairing a combination of the `e_j` with `h`. -/
theorem integral_sum_mul_conj {n : ℕ} {e : Fin n → ℝ → ℂ} {h : ℝ → ℂ} (a : Fin n → ℂ)
    (hint : ∀ j, Integrable fun u => e j u * conj (h u)) :
    ∫ u, (∑ j, a j * e j u) * conj (h u) = ∑ j, a j * ∫ u, e j u * conj (h u) := by
  have : (fun u => (∑ j, a j * e j u) * conj (h u)) = fun u => ∑ j, a j * (e j u * conj (h u)) := by
    funext u; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, integral_finsetSum _ fun j _ => (hint j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- The squared norm of a combination of an orthonormal family. -/
theorem integral_sum_mul_conj_sum {n : ℕ} {e : Fin n → ℝ → ℂ} (a : Fin n → ℂ)
    (hint : ∀ i j, Integrable fun u => e i u * conj (e j u))
    (horth : ∀ i j, ∫ u, e i u * conj (e j u) = if i = j then 1 else 0) :
    ∫ u, (∑ j, a j * e j u) * conj (∑ j, a j * e j u) = ∑ j, a j * conj (a j) := by
  have hint' : ∀ i, Integrable fun u => e i u * conj (∑ j, a j * e j u) := by
    intro i
    have : (fun u => e i u * conj (∑ j, a j * e j u)) =
        fun u => ∑ j, conj (a j) * (e i u * conj (e j u)) := by
      funext u; rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; ring
    rw [this]; exact integrable_finsetSum _ fun j _ => (hint i j).const_mul _
  rw [integral_sum_mul_conj a hint']
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun u => e i u * conj (∑ j, a j * e j u)) =
      fun u => ∑ j, conj (a j) * (e i u * conj (e j u)) := by
    funext u; rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; ring
  rw [this, integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  simp only [integral_const_mul, horth, mul_ite, mul_one, mul_zero]
  simp

/-- **Bessel's inequality.** For an `L²`-orthonormal family of continuous compactly supported
functions and a bounded measurable `h` with `‖h‖²` integrable, `Σ_j |⟨e_j, h⟩|² ≤ ‖h‖₂²`. -/
theorem sum_norm_sq_inner_le {n : ℕ} {e : Fin n → ℝ → ℂ} (he : ∀ j, Continuous (e j))
    (hec : ∀ j, HasCompactSupport (e j))
    (horth : ∀ i j, ∫ u, e i u * conj (e j u) = if i = j then 1 else 0) {h : ℝ → ℂ}
    (hhm : AEStronglyMeasurable h) (hhb : ∀ u, ‖h u‖ ≤ 1) (hh2 : Integrable fun u => ‖h u‖ ^ 2) :
    ∑ j, ‖∫ u, e j u * conj (h u)‖ ^ 2 ≤ ∫ u, ‖h u‖ ^ 2 := by
  set c : Fin n → ℂ := fun j => ∫ u, e j u * conj (h u) with hcdef
  set g : ℝ → ℂ := fun u => ∑ j, conj (c j) * e j u with hgdef
  set S := ∑ j, ‖c j‖ ^ 2 with hSdef
  have hgc : Continuous g := continuous_finsetSum _ fun j _ => continuous_const.mul (he j)
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_iUnion fun j => hec j) fun u hu => ?_
    simp only [hgdef]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [image_eq_zero_of_notMem_tsupport fun h => hu (Set.mem_iUnion.mpr ⟨j, h⟩), mul_zero]
  have hint_eh : ∀ j, Integrable fun u => e j u * conj (h u) := fun j =>
    Integrable.mono' ((he j).norm.integrable_of_hasCompactSupport (hec j).norm)
      ((he j).aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hhm))
      (Filter.Eventually.of_forall fun u => by
        rw [norm_mul, Complex.norm_conj]
        exact (mul_le_mul_of_nonneg_left (hhb u) (norm_nonneg _)).trans_eq (mul_one _))
  have hint_ee : ∀ i j, Integrable fun u => e i u * conj (e j u) := fun i j =>
    ((he i).mul (Complex.continuous_conj.comp (he j))).integrable_of_hasCompactSupport
      (hec i).mul_right
  have hS : ∀ j, conj (c j) * c j = ((‖c j‖ ^ 2 : ℝ) : ℂ) := fun j => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- `⟨g, h⟩ = S` and `⟨g, g⟩ = S`
  have hgh : ∫ u, g u * conj (h u) = S := by
    rw [hgdef, integral_sum_mul_conj _ hint_eh, hSdef]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    show conj (c j) * c j = _
    rw [hS j]; push_cast; ring
  have hgg : ∫ u, g u * conj (g u) = S := by
    rw [hgdef, integral_sum_mul_conj_sum _ hint_ee horth, hSdef]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.conj_conj, hS j]; push_cast; ring
  have hgh_int : Integrable fun u => g u * conj (h u) := by
    have : (fun u => g u * conj (h u)) = fun u => ∑ j, conj (c j) * (e j u * conj (h u)) := by
      funext u; simp only [hgdef, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact integrable_finsetSum _ fun j _ => (hint_eh j).const_mul _
  have hgg_int : Integrable fun u => g u * conj (g u) :=
    (hgc.mul (Complex.continuous_conj.comp hgc)).integrable_of_hasCompactSupport hgcs.mul_right
  exact bessel_core hh2 hgh_int hgg_int hgc hgcs hgh hgg

/-- The exponential window `u ↦ e^{−iτu}` on `[−A, A]`. -/
def expWindow (A τ : ℝ) : ℝ → ℂ := (Icc (-A) A).indicator fun u => Complex.exp (-(I * τ * u))

theorem norm_expWindow_le (A τ u : ℝ) : ‖expWindow A τ u‖ ≤ 1 := by
  rw [expWindow]
  by_cases hu : u ∈ Icc (-A) A
  · rw [Set.indicator_of_mem hu, Complex.norm_exp]; simp
  · rw [Set.indicator_of_notMem hu, norm_zero]; norm_num

theorem norm_sq_expWindow (A τ : ℝ) :
    (fun u => ‖expWindow A τ u‖ ^ 2) = (Icc (-A) A).indicator fun _ => (1 : ℝ) := by
  funext u
  rw [expWindow]
  by_cases hu : u ∈ Icc (-A) A
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Complex.norm_exp]; simp
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero]; norm_num

/-- Pairing with the window is the transform, for functions living on `[−A, A]`. -/
theorem integral_mul_conj_expWindow {f : ℝ → ℂ} {A : ℝ} (hfs : tsupport f ⊆ Icc (-A) A) (τ : ℝ) :
    ∫ u, f u * conj (expWindow A τ u) = paperFT f τ := by
  rw [paperFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show f u * conj (expWindow A τ u) = f u * Complex.exp (I * τ * u)
  rw [expWindow]
  by_cases hu : u ∈ Icc (-A) A
  · rw [Set.indicator_of_mem hu, ← Complex.exp_conj]
    congr 2
    simp [map_mul, Complex.conj_ofReal]
  · rw [Set.indicator_of_notMem hu, image_eq_zero_of_notMem_tsupport fun h => hu (hfs h)]
    simp

/-- **Bessel's inequality for the exponentials on `[−A, A]`.** -/
theorem sum_norm_sq_paperFT_le {n : ℕ} {e : Fin n → ℝ → ℂ} (he : ∀ j, Continuous (e j)) {A : ℝ}
    (hA : 0 ≤ A) (hes : ∀ j, tsupport (e j) ⊆ Icc (-A) A)
    (horth : ∀ i j, ∫ u, e i u * conj (e j u) = if i = j then 1 else 0) (τ : ℝ) :
    ∑ j, ‖paperFT (e j) τ‖ ^ 2 ≤ 2 * A := by
  have hec : ∀ j, HasCompactSupport (e j) := fun j =>
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport _).trans (hes j))
  have hm : AEStronglyMeasurable (expWindow A τ) :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg
      |>.aestronglyMeasurable).indicator measurableSet_Icc)
  have h2 : Integrable fun u => ‖expWindow A τ u‖ ^ 2 := by
    rw [norm_sq_expWindow]
    exact (integrableOn_const (s := Icc (-A) A) (μ := volume) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) enorm_ne_top).integrable_indicator
      measurableSet_Icc
  have hB := sum_norm_sq_inner_le he hec horth hm (norm_expWindow_le A τ) h2
  simp only [fun j => integral_mul_conj_expWindow (hes j) τ] at hB
  refine hB.trans_eq ?_
  rw [norm_sq_expWindow, integral_indicator_const _ measurableSet_Icc, Measure.real_def,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
  ring

/-- **Finitely many negative directions at every aperture.** -/
theorem card_negative_orthonormal_le {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, ∀ (n : ℕ) (e : Fin n → ℝ → ℂ), (∀ j, ContDiff ℝ 2 (e j)) →
      (∀ j, tsupport (e j) ⊆ Icc (-A) A) →
      (∀ i j, ∫ u, e i u * conj (e j u) = if i = j then 1 else 0) →
      (∀ j, (zetaZeroConfig.W (e j) (e j)).re < 0) → (n : ℝ) < B := by
  obtain ⟨T₀, K, hT₀, hK, hgard⟩ := re_W_ge_sub_lowMass hA
  refine ⟨2 * A * T₀ * K / π + 1, fun n e he hes horth hneg => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : 0 ≤ 2 * A * T₀ * K / π := by positivity
    push_cast; linarith
  have hπ := Real.pi_pos
  -- each direction carries low-frequency mass above `2π/K`
  have hnorm : ∀ j, ∫ u, ‖e j u‖ ^ 2 = 1 := by
    intro j
    have h := horth j j
    rw [if_pos rfl] at h
    have : (fun u => e j u * conj (e j u)) = fun u => ((‖e j u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, integral_complex_ofReal] at h
    exact_mod_cast h
  have hlow : ∀ j, 2 * π < K * lowMass T₀ (e j) := by
    intro j
    have := hgard (e j) (he j) (hes j)
    rw [hnorm, mul_one] at this
    linarith [hneg j]
  have hK0 : 0 < K := by
    by_contra h
    have hK' : K = 0 := le_antisymm (not_lt.mp h) hK
    have := hlow ⟨0, hn⟩
    rw [hK', zero_mul] at this
    linarith
  -- the total low-frequency mass is at most `4AT₀` (Bessel)
  have hec : ∀ j, HasCompactSupport (e j) := fun j =>
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport _).trans (hes j))
  have htotal : ∑ j, lowMass T₀ (e j) ≤ 2 * A * (2 * T₀) := by
    simp only [lowMass]
    rw [← integral_finsetSum _ fun j _ =>
      (integrable_norm_sq_paperFT_of_tests (he j) (hec j)).integrableOn]
    calc ∫ τ in Icc (-T₀) T₀, ∑ j, ‖paperFT (e j) τ‖ ^ 2 ≤ ∫ τ in Icc (-T₀) T₀, 2 * A :=
          setIntegral_mono_on (integrable_finsetSum _ fun j _ =>
            (integrable_norm_sq_paperFT_of_tests (he j) (hec j)).integrableOn)
            (continuousOn_const.integrableOn_compact isCompact_Icc) measurableSet_Icc
            fun τ _ => sum_norm_sq_paperFT_le (fun j => (he j).continuous) hA.le hes horth τ
      _ = 2 * A * (2 * T₀) := by
          rw [setIntegral_const, Measure.real_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          ring
  have hsum : (n : ℝ) * (2 * π / K) < ∑ j, lowMass T₀ (e j) := by
    calc (n : ℝ) * (2 * π / K) = ∑ _j : Fin n, 2 * π / K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < ∑ j, lowMass T₀ (e j) := by
          refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun j _ => ?_
          rw [div_lt_iff₀ hK0]
          linarith [hlow j]
  have hfin : (n : ℝ) * (2 * π / K) < 2 * A * (2 * T₀) := lt_of_lt_of_le hsum htotal
  have : (n : ℝ) < 2 * A * T₀ * K / π := by
    rw [lt_div_iff₀ hπ]
    have h2 : (n : ℝ) * (2 * π / K) * K = (n : ℝ) * (2 * π) := by field_simp
    nlinarith
  linarith

end GaloisForLFunctions.ArithmeticPolarization
