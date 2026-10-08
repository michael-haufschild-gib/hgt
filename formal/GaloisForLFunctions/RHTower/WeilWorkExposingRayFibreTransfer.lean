import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalResonator
import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Polar and full mass bounds for integer atomic forms

For every real coefficient sequence and constant, an upper bound by physical
L2 mass on all compact complex C2 polar sources holds exactly when it holds
on all compact complex C2 sources. Actual polar multiplicative resonators
supply a constant Toeplitz bound. Averaging translates over divisors of
powers of a fixed factorial transfers it to every compact source.

No atomic growth, positivity, RH, spectral representation or transference
premise is added. The gamma-weighted case has a logarithmic Toeplitz cost
and is not covered. This is a component of the paper all-fibre L1 density
argument, not the WP02 lower bound or a formal recovery theorem.

Paper: docs/reports/weil-work/results/02-exposing-ray/POLAR-FIBRE-DENSITY-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Zeta23 Complex
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open ResonatorProfile

private theorem divisors_pow_card {D : ℕ} (hD : D ≠ 0) (L : ℕ) :
    ((D^(L+1)).divisors.card : ℝ) =
      ∏ p ∈ D.primeFactors, (((L+1 : ℕ) : ℝ) * D.factorization p + 1) := by
  rw [Nat.card_divisors (pow_ne_zero _ hD), Nat.primeFactors_pow_succ]
  push_cast
  apply Finset.prod_congr rfl
  intro p _
  rw [Nat.factorization_pow, Finsupp.smul_apply]
  simp

private theorem consecutive_divisor_ratio {D : ℕ} (hD : D ≠ 0) :
    Tendsto (fun L : ℕ => ((D^(L+1)).divisors.card : ℝ) /
      ((D^(L+2)).divisors.card : ℝ)) atTop (𝓝 1) := by
  have hp (p : ℕ) (hp : p ∈ D.primeFactors) :
      Tendsto (fun L : ℕ => (((L+1 : ℕ) : ℝ) * D.factorization p + 1) /
        (((L+2 : ℕ) : ℝ) * D.factorization p + 1)) atTop (𝓝 1) := by
    have he : (D.factorization p : ℝ) ≠ 0 := by
      exact_mod_cast Finsupp.mem_support_iff.mp (Nat.support_factorization D ▸ hp)
    convert tendsto_add_mul_div_add_mul_atTop_nhds
      (1 + (D.factorization p : ℝ)) (1 + 2 * (D.factorization p : ℝ))
      (D.factorization p : ℝ) he using 1
    · funext L; push_cast; congr 1 <;> ring
    · rw [div_self he]
  have h := tendsto_finsetProd D.primeFactors hp
  convert h using 1
  · funext L
    rw [divisors_pow_card hD, show L+2 = (L+1)+1 by omega, divisors_pow_card hD,
      ← Finset.prod_div_distrib]
  · simp

private def overlapRatio (D L n : ℕ) : ℝ :=
  (((D^(L+2)).divisors.filter (fun m => n*m ∈ (D^(L+2)).divisors)).card : ℝ) /
    ((D^(L+2)).divisors.card : ℝ)

private theorem overlapRatio_le_one (D L n : ℕ) : overlapRatio D L n ≤ 1 := by
  unfold overlapRatio
  exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)

private theorem consecutive_le_overlapRatio {D n : ℕ} (hD : D ≠ 0) (hn : n ∣ D) (L : ℕ) :
    ((D^(L+1)).divisors.card : ℝ) / ((D^(L+2)).divisors.card : ℝ) ≤
      overlapRatio D L n := by
  have hsub : (D^(L+1)).divisors ⊆
      (D^(L+2)).divisors.filter (fun m => n*m ∈ (D^(L+2)).divisors) := by
    intro m hm
    have hd := Nat.dvd_of_mem_divisors hm
    apply Finset.mem_filter.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨hd.trans (Nat.pow_dvd_pow D (by omega)), pow_ne_zero _ hD⟩
    · apply Nat.mem_divisors.mpr
      refine ⟨?_, pow_ne_zero _ hD⟩
      convert Nat.mul_dvd_mul hn hd using 1
      rw [show L+2=(L+1)+1 by omega, pow_succ']
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)

private theorem tendsto_overlapRatio {D n : ℕ} (hD : D ≠ 0) (hn : n ∣ D) :
    Tendsto (fun L : ℕ => overlapRatio D L n) atTop (𝓝 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (consecutive_divisor_ratio hD) tendsto_const_nhds
    (Filter.Eventually.of_forall (consecutive_le_overlapRatio hD hn))
    (Filter.Eventually.of_forall (fun L => overlapRatio_le_one D L n))

private theorem corr_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (a b : ℝ) :
    Integrable (fun x : ℝ => f (x-a) * conj (f (x-b))) := by
  refine ((hf.comp (continuous_id.sub continuous_const)).mul
    (continuous_conj.comp (hf.comp (continuous_id.sub continuous_const)))).integrable_of_hasCompactSupport ?_
  exact (hfc.comp_homeomorph (Homeomorph.subRight a)).mul_right

private theorem corr_neg_re (f : ℝ → ℂ) (y : ℝ) :
    (EF.weilTest f f (-y)).re = (EF.weilTest f f y).re := by
  have heq : EF.weilTest f f (-y) = conj (EF.weilTest f f y) := by
    rw [weilTest_apply, weilTest_apply, ← integral_conj]
    rw [← integral_sub_right_eq_self (μ := volume) _ y]
    congr 1; funext t
    simp only [map_mul, Complex.conj_conj]
    rw [mul_comm]; congr 2; ring_nf
  rw [heq, Complex.conj_re]

private theorem integral_translated_corr {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∫ x : ℝ, (f (x-Real.log (n*m)) * conj (f (x-Real.log m))).re =
      atomCoeff f n / 2 := by
  have hire : (∫ x : ℝ, (f (x-Real.log ((n : ℝ)*m)) * conj (f (x-Real.log m))).re) =
      (∫ x : ℝ, f (x-Real.log ((n : ℝ)*m)) * conj (f (x-Real.log m))).re :=
    Complex.reCLM.integral_comp_comm (corr_integrable hf hfc _ _)
  rw [hire]
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => f (x-Real.log (n*m)) * conj (f (x-Real.log m))) (Real.log (n*m))
  have heq : (∫ x : ℝ, f (x-Real.log (n*m)) * conj (f (x-Real.log m))) =
      EF.weilTest f f (-Real.log n) := by
    rw [← hshift, weilTest_apply]
    congr 1; funext x
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    rw [Real.log_mul hn0 hm0]
    congr 2 <;> congr 1 <;> ring
  rw [heq, corr_neg_re, atomCoeff, Complex.add_re, corr_neg_re]
  ring

private theorem normSq_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (a : ℝ) :
    Integrable (fun x : ℝ => ‖f (x-a)‖^2) := by
  have hi := (corr_integrable hf hfc a a).re
  change Integrable (fun x : ℝ => (f (x-a) * conj (f (x-a))).re) at hi
  simpa only [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hi

private theorem re_sum (s : Finset ℕ) (g : ℕ → ℂ) :
    (∑ i ∈ s, g i).re = ∑ i ∈ s, (g i).re :=
  map_sum Complex.reAddGroupHom g s


private def masked (B : Finset ℕ) (f : ℝ → ℂ) (x : ℝ) (m : ℕ) : ℂ :=
  if m ∈ B then f (x-Real.log m) else 0

private theorem masked_corr_sum (B : Finset ℕ) {N : ℕ}
    (hB : B ⊆ Finset.Icc 1 N) (f : ℝ → ℂ) (x : ℝ) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, masked B f x (n*m) * conj (masked B f x m) =
      ∑ m ∈ B.filter (fun m => n*m ∈ B),
        f (x-Real.log (n*m)) * conj (f (x-Real.log m)) := by
  calc
    _ = ∑ m ∈ B, masked B f x (n*m) * conj (masked B f x m) := by
      symm
      exact Finset.sum_subset hB (fun m _ hm => by simp [masked, hm])
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [masked, if_pos hm]
      split_ifs <;> simp

private theorem masked_mass_sum (B : Finset ℕ) {N : ℕ}
    (hB : B ⊆ Finset.Icc 1 N) (f : ℝ → ℂ) (x : ℝ) :
    ∑ m ∈ Finset.Icc 1 N, ‖masked B f x m‖^2 =
      ∑ m ∈ B, ‖f (x-Real.log m)‖^2 := by
  calc
    _ = ∑ m ∈ B, ‖masked B f x m‖^2 := by
      symm
      exact Finset.sum_subset hB (fun m _ hm => by simp [masked, hm])
    _ = _ := Finset.sum_congr rfl (fun m hm => by simp [masked, hm])

/-- A constant multiplicative Toeplitz bound, in raw atom normalization. -/
def ConstantToeplitz (b : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ c : ℕ → ℂ, (∀ m, N < m → c m = 0) →
    2 * ∑ n ∈ Finset.Icc 2 N, b n *
      (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)).re ≤
        C * ∑ m ∈ Finset.Icc 1 N, ‖c m‖^2

private theorem finite_average {b : ℕ → ℝ} {C : ℝ} (h : ConstantToeplitz b C)
    {N : ℕ} (hN : 1≤N) (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 N)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∑ n ∈ Finset.Icc 2 N,
      b n * ((B.filter (fun m => n*m ∈ B)).card : ℝ) * atomCoeff f n ≤
      C * (B.card : ℝ) * ∫ x : ℝ, ‖f x‖^2 := by
  let A : ℕ → ℝ → ℝ := fun n x =>
    ∑ m ∈ B.filter (fun m => n*m ∈ B),
      (f (x-Real.log (n*m)) * conj (f (x-Real.log m))).re
  have hA (n : ℕ) : Integrable (A n) := by
    exact integrable_finsetSum _ (fun m _ => (corr_integrable hf hfc _ _).re)
  have hM : Integrable (fun x : ℝ => ∑ m ∈ B, ‖f (x-Real.log m)‖^2) :=
    integrable_finsetSum _ (fun m _ => normSq_integrable hf hfc _)
  have hpoint (x : ℝ) :
      2 * ∑ n ∈ Finset.Icc 2 N, b n * A n x ≤
        C * ∑ m ∈ B, ‖f (x-Real.log m)‖^2 := by
    have hh := h N hN (masked B f x) (fun m hm => by
      have hmB : m ∉ B := fun hb => by have := (Finset.mem_Icc.mp (hB hb)).2; omega
      simp [masked, hmB])
    simp_rw [masked_corr_sum B hB f x, re_sum] at hh
    rwa [masked_mass_sum B hB f x] at hh
  have hh := integral_mono
    ((integrable_finsetSum _ (fun n _ => (hA n).const_mul (b n))).const_mul 2)
    (hM.const_mul C) hpoint
  have hAi (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      ∫ x : ℝ, A n x = ((B.filter (fun m => n*m ∈ B)).card : ℝ) * (atomCoeff f n / 2) := by
    dsimp only [A]
    have hi (m : ℕ) : Integrable (fun x : ℝ =>
        (f (x-Real.log ((n : ℝ)*m)) * conj (f (x-Real.log m))).re) :=
      (corr_integrable hf hfc _ _).re
    rw [integral_finsetSum (B.filter (fun m => n*m ∈ B)) (fun m _ => hi m)]
    have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    calc
      _ = ∑ m ∈ B.filter (fun m => n*m ∈ B), atomCoeff f n / 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        exact integral_translated_corr hf hfc hn0
          (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (hB (Finset.mem_filter.mp hm).1)).1)
      _ = _ := by simp
  have hMi : (∫ x : ℝ, ∑ m ∈ B, ‖f (x-Real.log m)‖^2) =
      (B.card : ℝ) * ∫ x : ℝ, ‖f x‖^2 := by
    rw [integral_finsetSum B (fun m _ => normSq_integrable hf hfc (Real.log m))]
    calc
      _ = ∑ m ∈ B, ∫ x : ℝ, ‖f x‖^2 :=
        Finset.sum_congr rfl (fun m _ => integral_sub_right_eq_self (fun x : ℝ => ‖f x‖^2) (Real.log m))
      _ = _ := by simp
  rw [integral_const_mul, integral_finsetSum _ (fun n _ => (hA n).const_mul (b n)),
    integral_const_mul, hMi] at hh
  simp_rw [integral_const_mul] at hh
  have heq : (2:ℝ) * ∑ n ∈ Finset.Icc 2 N, b n * (∫ x : ℝ, A n x) =
      ∑ n ∈ Finset.Icc 2 N,
        b n * ((B.filter (fun m => n*m ∈ B)).card : ℝ) * atomCoeff f n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hAi n hn]
    ring
  rw [heq] at hh
  simpa [mul_assoc] using hh

/-- Transfer the constant multiplicative inequality to arbitrary compact complex sources. -/
theorem constantToeplitz_transfer {b : ℕ → ℝ} {C : ℝ} (h : ConstantToeplitz b C)
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Set.Icc (-a) a) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n * atomCoeff f n ≤
      C * ∫ x : ℝ, ‖f x‖^2 := by
  let M : ℕ := max 2 ⌊Real.exp (2*a)⌋₊
  let D : ℕ := M.factorial
  have hD : D ≠ 0 := Nat.factorial_ne_zero M
  have hfcs : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hzero (n : ℕ) (hn : ⌊Real.exp (2*a)⌋₊ < n) : atomCoeff f n=0 :=
    atomCoeff_eq_zero_of_floor_lt hfs hn
  have havg (L : ℕ) :
      ∑ n ∈ Finset.Icc 2 M, b n * overlapRatio D L n * atomCoeff f n ≤
        C * ∫ x : ℝ, ‖f x‖^2 := by
    let B := (D^(L+2)).divisors
    let N := D^(L+2)+M
    have hBN : B ⊆ Finset.Icc 1 N := by
      intro m hm
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hm,
        (Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hD) _) (Nat.dvd_of_mem_divisors hm)).trans
          (Nat.le_add_right _ _)⟩
    have hN : 1≤N := by dsimp [N,M]; omega
    have hh := finite_average h hN B hBN hf.continuous hfcs
    have hMN : M≤N := Nat.le_add_left _ _
    have heq : (∑ n ∈ Finset.Icc 2 M,
        b n * ((B.filter (fun m => n*m ∈ B)).card : ℝ) * atomCoeff f n) =
        ∑ n ∈ Finset.Icc 2 N,
          b n * ((B.filter (fun m => n*m ∈ B)).card : ℝ) * atomCoeff f n := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right hMN)
      intro n hn hnot
      have hlt : M<n := by
        have hn2 := (Finset.mem_Icc.mp hn).1
        by_contra hh; exact hnot (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
      rw [hzero n (lt_of_le_of_lt (Nat.le_max_right _ _) hlt), mul_zero]
    rw [← heq] at hh
    have hcard : (0:ℝ) < B.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero _ hD)⟩
    have hdiv : (∑ n ∈ Finset.Icc 2 M,
        b n * ((B.filter (fun m => n*m ∈ B)).card : ℝ) * atomCoeff f n) / B.card ≤
        C * ∫ x : ℝ, ‖f x‖^2 := by
      apply (div_le_iff₀ hcard).mpr
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
    have hid : (∑ n ∈ Finset.Icc 2 M,
        b n * ((B.filter (fun m => n*m ∈ B)).card : ℝ) * atomCoeff f n) / B.card =
        ∑ n ∈ Finset.Icc 2 M, b n * overlapRatio D L n * atomCoeff f n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      dsimp [overlapRatio,B]
      ring
    rw [hid] at hdiv
    exact hdiv
  have hlim : Tendsto (fun L : ℕ =>
      ∑ n ∈ Finset.Icc 2 M, b n * overlapRatio D L n * atomCoeff f n)
      atTop (𝓝 (∑ n ∈ Finset.Icc 2 M, b n * atomCoeff f n)) := by
    convert tendsto_finsetSum (Finset.Icc 2 M) (fun n hn =>
      ((tendsto_overlapRatio hD (Nat.dvd_factorial
        (by have := (Finset.mem_Icc.mp hn).1; omega) (Finset.mem_Icc.mp hn).2)).const_mul
          (b n)).mul_const (atomCoeff f n)) using 1; simp
  have hh := le_of_tendsto hlim (Filter.Eventually.of_forall havg)
  have heq : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n * atomCoeff f n) =
      ∑ n ∈ Finset.Icc 2 M, b n * atomCoeff f n := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.le_max_right _ _))
    intro n hn hnot
    have hlt : ⌊Real.exp (2*a)⌋₊ < n := by
      have hn2 := (Finset.mem_Icc.mp hn).1
      by_contra hh; exact hnot (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
    rw [hzero n hlt, mul_zero]
  rwa [← heq] at hh

/-- Raw atomic forms bounded above by physical mass on the actual polar class. -/
def PolarMassBound (b : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ a : ℝ, ∀ f : ℝ → ℂ, IsPolarTest a f →
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n * atomCoeff f n ≤
      C * ∫ x : ℝ, ‖f x‖^2

/-- The same upper bound without the two pole constraints. -/
def FullMassBound (b : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Set.Icc (-a) a →
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n * atomCoeff f n ≤
      C * ∫ x : ℝ, ‖f x‖^2

private theorem constantToeplitz_of_polarMassBound {b : ℕ → ℝ} {C : ℝ}
    (h : PolarMassBound b C) : ConstantToeplitz b C := by
  intro N hN c hc
  let w : ℝ := 1 / ((N : ℝ)+1)
  let a : ℝ := Real.log N / 2 + w/4
  let f : ℝ → ℂ := resonator N c w
  have hw : 0 < w := by dsimp [w]; positivity
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNr
  have hp := paperFT_resonator_pole (N := N) (c := c) hw
  have hpol : IsPolarTest a f := by
    refine ⟨?_, contDiff_resonator N c w 2, ?_, hp.1, hp.2⟩
    · dsimp [a]; exact add_nonneg (div_nonneg (Real.log_nonneg hNr) (by norm_num)) (by positivity)
    · exact tsupport_subset_of_vanish (fun u hu =>
        sum_translates_eq_zero (fun v hv => gC_eq_zero hw hv) hu)
  have hK : N ≤ ⌊Real.exp (2*a)⌋₊ := by
    apply Nat.le_floor
    calc
      (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0).symm
      _ ≤ Real.exp (2*a) := Real.exp_le_exp.mpr (by dsimp [a]; linarith)
  have hcorr (n : ℕ) (hn : 1 ≤ n) : atomCoeff f n =
      2 * WeilWorkPBAP.resonatorMass N *
        (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)).re :=
    WeilWorkPBAP.resonator_log_sample N c hc n hn
  have htail (n : ℕ) (hn : N < n) : atomCoeff f n = 0 := by
    rw [hcorr n (by omega)]
    have hz : (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmn : N < n*m := lt_of_lt_of_le hn (Nat.le_mul_of_pos_right n (Finset.mem_Icc.mp hm).1)
      rw [hc (n*m) hmn, zero_mul]
    rw [hz, Complex.zero_re, mul_zero]
  have hh := h a f hpol
  have heq : (∑ n ∈ Finset.Icc 2 N, b n * atomCoeff f n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n * atomCoeff f n := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right hK)
    intro n hn hnot
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hlt : N < n := by
      by_contra hle; exact hnot (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
    rw [htail n hlt, mul_zero]
  rw [← heq] at hh
  have hm : (∫ x : ℝ, ‖f x‖^2) =
      WeilWorkPBAP.resonatorMass N * ∑ m ∈ Finset.Icc 1 N, ‖c m‖^2 :=
    WeilWorkPBAP.resonator_mass hN c hc
  rw [hm] at hh
  have he : (∑ n ∈ Finset.Icc 2 N, b n * atomCoeff f n) =
      WeilWorkPBAP.resonatorMass N *
        (2 * ∑ n ∈ Finset.Icc 2 N, b n *
          (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)).re) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcorr n (by have := (Finset.mem_Icc.mp hn).1; omega)]
    ring
  rw [he] at hh
  have hprod : WeilWorkPBAP.resonatorMass N *
      (2 * ∑ n ∈ Finset.Icc 2 N, b n *
        (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)).re) ≤
      WeilWorkPBAP.resonatorMass N * (C * ∑ m ∈ Finset.Icc 1 N, ‖c m‖^2) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  exact le_of_mul_le_mul_left hprod (WeilWorkPBAP.resonatorMass_pos N)

/-- Polar restriction is invisible to a constant physical-mass upper bound on integer atoms.
This equivalence is unconditional in the coefficient sequence and the bound. -/
theorem polarMassBound_iff_fullMassBound (b : ℕ → ℝ) (C : ℝ) :
    PolarMassBound b C ↔ FullMassBound b C := by
  constructor
  · intro h a f hf hfs
    exact constantToeplitz_transfer (constantToeplitz_of_polarMassBound h) hf hfs
  · intro h a f hf
    exact h a f hf.2.1 hf.2.2.1

end RHTower.ExposingRayTransfer
