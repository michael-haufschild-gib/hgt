import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeKernel
import GaloisForLFunctions.RHTower.ChiPrimeGaussianProgressionProfile
import GaloisForLFunctions.HTGeometry.BoundedVariationRiemannSum

/-!
# Variation of the actual ordered hyperbolic prime kernel

The hyperbolic support length compensates the phase derivative. Every sharp
cutoff contributes its jumps before the prime pairs are summed.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower
namespace RHTower

private theorem variation_le_of_norm_sum {f : ℝ → ℂ} {s : Set ℝ} {B : ℝ}
    (h : ∀ (n : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ s) →
      ∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖ ≤ B) :
    eVariationOn f s ≤ ENNReal.ofReal B := by
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  simp only [edist_dist, dist_eq_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (h n u hu hs)

private theorem norm_sum_le_variation_bound {f : ℝ → ℂ} {s : Set ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hV : eVariationOn f s ≤ ENNReal.ofReal B)
    (n : ℕ) (u : ℕ → ℝ) (hu : Monotone u) (hs : ∀ i, u i ∈ s) :
    ∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖ ≤ B := by
  apply (ENNReal.ofReal_le_ofReal_iff hB).1
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  simpa only [edist_dist, dist_eq_norm] using (eVariationOn.sum_le hu hs (n := n)).trans hV

private theorem variation_mul_le {f g : ℝ → ℂ} {s : Set ℝ} {A B U V : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hf : ∀ x ∈ s, ‖f x‖ ≤ A) (hg : ∀ x ∈ s, ‖g x‖ ≤ B)
    (hfV : eVariationOn f s ≤ ENNReal.ofReal U)
    (hgV : eVariationOn g s ≤ ENNReal.ofReal V) :
    eVariationOn (fun x => f x * g x) s ≤ ENNReal.ofReal (B * U + A * V) := by
  apply variation_le_of_norm_sum
  intro n u hu hs
  have hterm (i : ℕ) : ‖f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i)‖ ≤
      B * ‖f (u (i + 1)) - f (u i)‖ + A * ‖g (u (i + 1)) - g (u i)‖ := by
    calc
      _ = ‖g (u (i + 1)) * (f (u (i + 1)) - f (u i)) +
        f (u i) * (g (u (i + 1)) - g (u i))‖ := by congr 1; ring
      _ ≤ ‖g (u (i + 1))‖ * ‖f (u (i + 1)) - f (u i)‖ +
        ‖f (u i)‖ * ‖g (u (i + 1)) - g (u i)‖ := by
          exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (hg _ (hs _)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hf _ (hs _)) (norm_nonneg _))
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (B * ‖f (u (i + 1)) - f (u i)‖ + A * ‖g (u (i + 1)) - g (u i)‖) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = B * (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) +
        A * (∑ i ∈ Finset.range n, ‖g (u (i + 1)) - g (u i)‖) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_sum_le_variation_bound hU hfV n u hu hs) hB)
      (mul_le_mul_of_nonneg_left (norm_sum_le_variation_bound hV hgV n u hu hs) hA)

private theorem variation_sub_le {f g : ℝ → ℂ} {s : Set ℝ} {U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hfV : eVariationOn f s ≤ ENNReal.ofReal U)
    (hgV : eVariationOn g s ≤ ENNReal.ofReal V) :
    eVariationOn (fun x => f x - g x) s ≤ ENNReal.ofReal (U + V) := by
  apply variation_le_of_norm_sum
  intro n u hu hs
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (‖f (u (i + 1)) - f (u i)‖ + ‖g (u (i + 1)) - g (u i)‖) := by
      apply Finset.sum_le_sum
      intro i _
      have heq : f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i)) =
          (f (u (i + 1)) - f (u i)) - (g (u (i + 1)) - g (u i)) := by ring
      rw [heq]
      exact norm_sub_le _ _
    _ ≤ U + V := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (norm_sum_le_variation_bound hU hfV n u hu hs)
        (norm_sum_le_variation_bound hV hgV n u hu hs)

private theorem variation_monotone_unit {f : ℝ → ℝ} (hf : Monotone f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    eVariationOn (fun x => (f x : ℂ)) Set.univ ≤ ENNReal.ofReal 1 := by
  apply variation_le_of_norm_sum
  intro n u hu _
  calc
    _ = ∑ i ∈ Finset.range n, (f (u (i + 1)) - f (u i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_nonneg.mpr (hf (hu (Nat.le_succ i))))]
    _ = f (u n) - f (u 0) := Finset.sum_range_sub (fun i => f (u i)) n
    _ ≤ 1 := by linarith [hf1 (u n), hf0 (u 0)]

private theorem variation_step (P : ℝ → Prop) [DecidablePred P]
    (hP : ∀ x y, x ≤ y → P x → P y) :
    eVariationOn (fun x => if P x then (1 : ℂ) else 0) Set.univ ≤ ENNReal.ofReal 1 := by
  classical
  have hm : Monotone (fun x => if P x then (1 : ℝ) else 0) := by
    intro x y hxy
    by_cases hx : P x
    · simp only [if_pos hx, if_pos (hP x y hxy hx), le_refl]
    · simp only [if_neg hx]
      split_ifs <;> norm_num
  have h := variation_monotone_unit hm
    (fun x => by split_ifs <;> norm_num) (fun x => by split_ifs <;> norm_num)
  simpa only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h

private theorem variation_indicator_Icc {a b : ℝ} (hab : a ≤ b) :
    eVariationOn ((Set.Icc a b).indicator (fun _ => (1 : ℂ))) Set.univ ≤ ENNReal.ofReal 2 := by
  classical
  have ha := variation_step (fun x => a ≤ x) (fun x y hxy hx => hx.trans hxy)
  have hb := variation_step (fun x => b < x) (fun x y hxy hx => hx.trans_le hxy)
  have h := variation_sub_le (by norm_num) (by norm_num) ha hb
  have heq : (Set.Icc a b).indicator (fun _ => (1 : ℂ)) =
      fun x => (if a ≤ x then 1 else 0) - (if b < x then 1 else 0) := by
    funext x
    simp only [Set.indicator_apply, Set.mem_Icc]
    split_ifs <;> simp_all <;> linarith
  simpa only [← heq, one_add_one_eq_two] using h

private theorem variation_indicator_Ioc {a b : ℝ} (hab : a ≤ b) :
    eVariationOn ((Set.Ioc a b).indicator (fun _ => (1 : ℂ))) Set.univ ≤ ENNReal.ofReal 2 := by
  classical
  have ha := variation_step (fun x => a < x) (fun x y hxy hx => hx.trans_le hxy)
  have hb := variation_step (fun x => b < x) (fun x y hxy hx => hx.trans_le hxy)
  have h := variation_sub_le (by norm_num) (by norm_num) ha hb
  have heq : (Set.Ioc a b).indicator (fun _ => (1 : ℂ)) =
      fun x => (if a < x then 1 else 0) - (if b < x then 1 else 0) := by
    funext x
    simp only [Set.indicator_apply, Set.mem_Ioc]
    split_ifs <;> simp_all <;> linarith
  simpa only [← heq, one_add_one_eq_two] using h

private theorem variation_one_sub {f : ℝ → ℂ} {s : Set ℝ} {V : ℝ}
    (hV : eVariationOn f s ≤ ENNReal.ofReal V) :
    eVariationOn (fun x => 1 - f x) s ≤ ENNReal.ofReal V := by
  have heq : eVariationOn (fun x => 1 - f x) s = eVariationOn f s := by
    unfold eVariationOn
    congr 1
    funext p
    apply Finset.sum_congr rfl
    intro i _
    simp only [edist_dist, dist_eq_norm]
    rw [show (1 - f (p.2.1 (i + 1))) - (1 - f (p.2.1 i)) =
      -(f (p.2.1 (i + 1)) - f (p.2.1 i)) by ring, norm_neg]
  rw [heq]
  exact hV

private theorem norm_unit_indicator (S : Set ℝ) (x : ℝ) :
    ‖S.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ S <;> simp [hx]

private theorem variation_three_cutoffs {N r d R : ℝ} (hN : 0 ≤ N)
    (hd : 0 ≤ d) (hR : 0 ≤ R) :
    eVariationOn ((Set.Ioc N (2 * N) ∩ Set.Icc (r - R) (r + R) ∩
      (Set.Icc (r - d) (r + d))ᶜ).indicator (fun _ => (1 : ℂ))) Set.univ ≤ ENNReal.ofReal 6 := by
  classical
  let f := (Set.Ioc N (2 * N)).indicator (fun _ => (1 : ℂ))
  let g := (Set.Icc (r - R) (r + R)).indicator (fun _ => (1 : ℂ))
  let h := ((Set.Icc (r - d) (r + d))ᶜ).indicator (fun _ => (1 : ℂ))
  have hf : eVariationOn f Set.univ ≤ ENNReal.ofReal 2 := variation_indicator_Ioc (by linarith)
  have hg : eVariationOn g Set.univ ≤ ENNReal.ofReal 2 := variation_indicator_Icc (by linarith)
  have hh : eVariationOn h Set.univ ≤ ENNReal.ofReal 2 := by
    have heq : h = fun x => 1 - (Set.Icc (r - d) (r + d)).indicator (fun _ => (1 : ℂ)) x := by
      funext x
      by_cases hx : x ∈ Set.Icc (r - d) (r + d) <;> simp [h, hx]
    rw [heq]
    exact variation_one_sub (variation_indicator_Icc (by linarith))
  have hfg : eVariationOn (fun x => f x * g x) Set.univ ≤ ENNReal.ofReal 4 := by
    have hb := variation_mul_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun x _ => norm_unit_indicator _ x) (fun x _ => norm_unit_indicator _ x) hf hg
    norm_num at hb ⊢
    exact hb
  have hb := variation_mul_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (f := fun x => f x * g x) (g := h) (A := 1) (B := 1)
    (fun x _ => by
      rw [norm_mul]
      exact (mul_le_mul (norm_unit_indicator _ x) (norm_unit_indicator _ x)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
    (fun x _ => norm_unit_indicator _ x) hfg hh
  have heq : (Set.Ioc N (2 * N) ∩ Set.Icc (r - R) (r + R) ∩
      (Set.Icc (r - d) (r + d))ᶜ).indicator (fun _ => (1 : ℂ)) = fun x => f x * g x * h x := by
    funext x
    by_cases hx : x ∈ Set.Ioc N (2 * N) <;>
      by_cases hy : x ∈ Set.Icc (r - R) (r + R) <;>
      by_cases hz : x ∈ Set.Icc (r - d) (r + d) <;>
      simp [f, g, h, hx, hy, hz]
  rw [heq]
  norm_num at hb ⊢
  exact hb

private theorem variation_clamp_le {f : ℝ → ℂ} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ‖f y - f x‖ ≤ L * |y - x|) :
    eVariationOn (fun x => f (Set.projIcc a b hab x)) Set.univ ≤ ENNReal.ofReal (L * (b - a)) := by
  apply variation_le_of_norm_sum
  intro n u hu _
  let v : ℕ → ℝ := fun i => Set.projIcc a b hab (u i)
  have hv : Monotone v := fun i j hij => Set.monotone_projIcc hab (hu hij)
  calc
    _ ≤ ∑ i ∈ Finset.range n, L * (v (i + 1) - v i) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hlip (v i) (Set.projIcc a b hab (u i)).property
        (v (i + 1)) (Set.projIcc a b hab (u (i + 1))).property
      rwa [abs_of_nonneg (sub_nonneg.mpr (hv (Nat.le_succ i)))] at hi
    _ = L * (v n - v 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ L * (b - a) := mul_le_mul_of_nonneg_left
      (sub_le_sub (Set.projIcc a b hab (u n)).property.2
        (Set.projIcc a b hab (u 0)).property.1) hL

private def hyperbolicAmplitudeCoefficient (N : ℝ) (p r : ℕ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * smoothAFECutoff ((p : ℝ) / N) *
    (starRingEnd ℂ) (smoothAFECutoff ((r : ℝ) / N)) / (r : ℂ) / (Real.log N : ℂ)

private theorem hyperbolic_amplitude_factor {N x : ℝ} (hN : 1 < N)
    (hx : x ∈ Set.Icc N (2 * N)) (p r : ℕ) :
    chiCubicHyperbolicPrimeAmplitude N (p, r) x =
      hyperbolicAmplitudeCoefficient N p r *
        primeGaussianScaledLogProfile ((p : ℝ) / r) (1 / Real.log N) (x / N) *
          bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r)) := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := hN0.trans_le hx.1
  have hL : (Real.log N : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hN).ne'
  unfold chiCubicHyperbolicPrimeAmplitude hyperbolicAmplitudeCoefficient
    primeGaussianScaledLogProfile primeGaussianScaledProfile
  rw [show (p : ℝ) / r * (x / N) = (p : ℝ) * x / ((r : ℝ) * N) by ring,
    Real.log_div hx0.ne' hN0.ne']
  push_cast only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
  have hden : 1 + 1 / (Real.log N : ℂ) * ((Real.log x : ℂ) - (Real.log N : ℂ)) =
      (Real.log x : ℂ) / (Real.log N : ℂ) := by field_simp; ring
  rw [hden, inv_div]
  field_simp [hL]

private theorem hyperbolic_coefficient_norm {N : ℝ} (hN : 1 < N) {p r : ℕ}
    (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N) :
    ‖hyperbolicAmplitudeCoefficient N p r‖ ≤ 2 * Real.pi / (N * Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hpN := (primeProfileBand_mem hN0.le hp).2.1
  have hrN := (primeProfileBand_mem hN0.le hr).2.1
  have hL := Real.log_pos hN
  have hpV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hpN) hN0)
  have hrV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hrN) hN0)
  simp only [hyperbolicAmplitudeCoefficient, norm_div, norm_mul, Complex.norm_conj,
    Complex.norm_natCast]
  rw [Complex.norm_of_nonneg (show 0 ≤ 2 * Real.pi by positivity),
    Complex.norm_of_nonneg hL.le]
  calc
    _ ≤ 2 * Real.pi * 1 * 1 / N / Real.log N := by gcongr
    _ = _ := by ring

/-- One constant controls the spatial Lipschitz bound of the actual recentered
amplitude over every prime pair and every sufficiently positive band. -/
theorem exists_chiCubicHyperbolicPrimeAmplitude_lipschitz :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 < N → 1 ≤ Real.log N →
      ∀ p ∈ primeProfileBand N, ∀ r ∈ primeProfileBand N,
      ∀ x ∈ Set.Icc N (2 * N), ∀ y ∈ Set.Icc N (2 * N),
      ‖chiCubicHyperbolicPrimeAmplitude N (p, r) y -
        chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤
        C * (|(p : ℝ) - r| + 1) / (N ^ 2 * Real.log N) * |y - x| := by
  obtain ⟨B, hB, hF⟩ := exists_primeGaussianScaledLogProfile_lipschitz
  let C : ℝ := 2 * Real.pi * (2 * (B : ℝ) + 2 * Real.pi * B)
  have hB0 : (0 : ℝ) < B := hB
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN hlog p hp r hr x hx y hy
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := by linarith
  have hpN := (primeProfileBand_mem hN0.le hp).2
  have hrN := (primeProfileBand_mem hN0.le hr).2
  have hr0 : (0 : ℝ) < r := hN0.trans hrN.1
  have hξ : (p : ℝ) / r ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hr0).2
      linarith [hpN.1, hrN.2]
    · apply (div_le_iff₀ hr0).2
      linarith [hpN.2, hrN.1]
  have hl : 1 / Real.log N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hL).2 hlog⟩
  have hxy (z : ℝ) (hz : z ∈ Set.Icc N (2 * N)) : z / N ∈ Set.Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hN0).2 (by simpa using hz.1),
      (div_le_iff₀ hN0).2 hz.2⟩
  let g := fun z : ℝ => primeGaussianScaledLogProfile ((p : ℝ) / r) (1 / Real.log N) (z / N)
  let e := fun z : ℝ => bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (z - r) / r))
  have hg : ‖g x‖ ≤ B := (hF _ hξ _ hl).1 _ (hxy x hx)
  have hgd : ‖g y - g x‖ ≤ (2 * (B : ℝ) / N) * |y - x| := by
    have h := (hF _ hξ _ hl).2.dist_le_mul _ (hxy y hy) _ (hxy x hx)
    rw [dist_eq_norm, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hN0] at h
    change ‖g y - g x‖ ≤ (2 * (B : ℝ)) * (|y - x| / N) at h
    convert h using 1; ring
  have hed : ‖e y - e x‖ ≤ (2 * Real.pi * |(p : ℝ) - r| / N) * |y - x| := by
    calc
      _ ≤ |2 * Real.pi * (((p : ℝ) - r) * (y - r) / r) -
          2 * Real.pi * (((p : ℝ) - r) * (x - r) / r)| := norm_bourgainOscillation_sub_le _ _
      _ = (2 * Real.pi * |(p : ℝ) - r| / r) * |y - x| := by
        rw [show 2 * Real.pi * (((p : ℝ) - r) * (y - r) / r) -
          2 * Real.pi * (((p : ℝ) - r) * (x - r) / r) =
            (2 * Real.pi * ((p : ℝ) - r) / r) * (y - x) by ring]
        rw [abs_mul, abs_div, abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity),
          abs_of_pos hr0]
      _ ≤ _ := by
        gcongr
        exact hrN.1.le
  have hge : ‖g y * e y - g x * e x‖ ≤
      ((2 * (B : ℝ) + B * (2 * Real.pi * |(p : ℝ) - r|)) / N) * |y - x| := by
    calc
      _ = ‖(g y - g x) * e y + g x * (e y - e x)‖ := by congr 1; ring
      _ ≤ ‖g y - g x‖ * ‖e y‖ + ‖g x‖ * ‖e y - e x‖ := by
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ (2 * (B : ℝ) / N) * |y - x| * 1 +
          B * ((2 * Real.pi * |(p : ℝ) - r| / N) * |y - x|) := by
        exact add_le_add (mul_le_mul hgd (le_of_eq (norm_bourgainOscillation _))
          (norm_nonneg _) (by positivity)) (mul_le_mul hg hed (norm_nonneg _) B.coe_nonneg)
      _ = _ := by ring
  rw [hyperbolic_amplitude_factor hN hx, hyperbolic_amplitude_factor hN hy,
    show hyperbolicAmplitudeCoefficient N p r * g y * e y -
      hyperbolicAmplitudeCoefficient N p r * g x * e x =
        hyperbolicAmplitudeCoefficient N p r * (g y * e y - g x * e x) by ring, norm_mul]
  calc
    _ ≤ (2 * Real.pi / (N * Real.log N)) *
        (((2 * (B : ℝ) + B * (2 * Real.pi * |(p : ℝ) - r|)) / N) * |y - x|) :=
      mul_le_mul (hyperbolic_coefficient_norm hN hp hr) hge (norm_nonneg _) (by positivity)
    _ ≤ C * (|(p : ℝ) - r| + 1) / (N ^ 2 * Real.log N) * |y - x| := by
      have hb : 2 * (B : ℝ) + B * (2 * Real.pi * |(p : ℝ) - r|) ≤
          (2 * (B : ℝ) + 2 * Real.pi * B) * (|(p : ℝ) - r| + 1) := by
        nlinarith [abs_nonneg ((p : ℝ) - r), Real.pi_pos]
      have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hN0.le)
        (show 0 ≤ 2 * Real.pi / (N * Real.log N) by positivity)
      have hh' := mul_le_mul_of_nonneg_right hh (abs_nonneg (y - x))
      calc
        _ = (2 * Real.pi / (N * Real.log N) *
            ((2 * (B : ℝ) + B * (2 * Real.pi * |(p : ℝ) - r|)) / N)) * |y - x| := by ring
        _ ≤ (2 * Real.pi / (N * Real.log N) *
            ((2 * (B : ℝ) + 2 * Real.pi * B) * (|(p : ℝ) - r| + 1) / N)) * |y - x| := hh'
        _ = _ := by dsimp only [C]; field_simp

private theorem variation_indicator_lipschitz {f : ℝ → ℂ} {S : Set ℝ} {a b A L V : ℝ}
    (hab : a ≤ b) (hA : 0 ≤ A) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hsub : S ⊆ Set.Icc a b) (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ A)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ‖f y - f x‖ ≤ L * |y - x|)
    (hSV : eVariationOn (S.indicator (fun _ => (1 : ℂ))) Set.univ ≤ ENNReal.ofReal V) :
    eVariationOn (S.indicator f) Set.univ ≤ ENNReal.ofReal (L * (b - a) + A * V) := by
  classical
  let g := fun x : ℝ => f (Set.projIcc a b hab x)
  have hg : ∀ x ∈ Set.univ, ‖g x‖ ≤ A := fun x _ => hf _ (Set.projIcc a b hab x).property
  have h := variation_mul_le hA (by norm_num) (mul_nonneg hL (sub_nonneg.mpr hab)) hV hg
    (fun x _ => norm_unit_indicator S x) (variation_clamp_le hab hL hlip) hSV
  have heq : S.indicator f = fun x => g x * S.indicator (fun _ => (1 : ℂ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx, g, Set.projIcc_of_mem, hsub hx]
    · simp [hx]
  rw [heq]
  simpa only [one_mul] using h

private theorem hyperbolic_support_eq {N : ℝ} (M : ℕ) {p r : ℕ} (hne : p ≠ r) :
    chiCubicHyperbolicPrimeSupport N M (p, r) =
      Set.Ioc N (2 * N) ∩
        Set.Icc ((r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r|)
          ((r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r|) ∩
        (Set.Icc ((r : ℝ) - |(p : ℝ) - r|) ((r : ℝ) + |(p : ℝ) - r|))ᶜ := by
  have hd : 0 < |(p : ℝ) - r| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  ext x
  have hprod : |(p : ℝ) - r| * |x - r| ≤ (M : ℝ) * r ↔
      |x - r| ≤ (M : ℝ) * r / |(p : ℝ) - r| := by
    rw [le_div_iff₀ hd, mul_comm]
  have hcut (R : ℝ) : |x - r| ≤ R ↔ (r : ℝ) - R ≤ x ∧ x ≤ (r : ℝ) + R := by
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hord : |(p : ℝ) - r| < |x - r| ↔
      ¬((r : ℝ) - |(p : ℝ) - r| ≤ x ∧ x ≤ (r : ℝ) + |(p : ℝ) - r|) := by
    rw [← not_le, hcut]
  change (x ∈ Set.Ioc N (2 * N) ∧ |(p : ℝ) - r| < |x - r| ∧
      |(p : ℝ) - r| * |x - r| ≤ (M : ℝ) * r) ↔
    (x ∈ Set.Ioc N (2 * N) ∧
      ((r : ℝ) - (M : ℝ) * r / |(p : ℝ) - r| ≤ x ∧
        x ≤ (r : ℝ) + (M : ℝ) * r / |(p : ℝ) - r|)) ∧
      ¬((r : ℝ) - |(p : ℝ) - r| ≤ x ∧ x ≤ (r : ℝ) + |(p : ℝ) - r|)
  rw [hord, hprod, hcut]
  tauto

private theorem variation_hyperbolic_support {N : ℝ} (hN : 0 ≤ N) (M : ℕ)
    {p r : ℕ} (hne : p ≠ r) :
    eVariationOn ((chiCubicHyperbolicPrimeSupport N M (p, r)).indicator
      (fun _ => (1 : ℂ))) Set.univ ≤ ENNReal.ofReal 6 := by
  rw [hyperbolic_support_eq M hne]
  exact variation_three_cutoffs hN (abs_nonneg _) (by positivity)

private theorem prime_gap_one_le {p r : ℕ} (hne : p ≠ r) :
    1 ≤ |(p : ℝ) - r| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (p : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hh : (r : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem variation_hyperbolic_pair {N C : ℝ} (hN : 1 < N) (hC : 0 < C)
    (M : ℕ) {p r : ℕ} (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N)
    (hne : p ≠ r)
    (hlip : ∀ x ∈ Set.Icc N (2 * N), ∀ y ∈ Set.Icc N (2 * N),
      ‖chiCubicHyperbolicPrimeAmplitude N (p, r) y -
        chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤
        C * (|(p : ℝ) - r| + 1) / (N ^ 2 * Real.log N) * |y - x|) :
    eVariationOn ((chiCubicHyperbolicPrimeSupport N M (p, r)).indicator
      (chiCubicHyperbolicPrimeAmplitude N (p, r))) Set.univ ≤
        ENNReal.ofReal ((8 * C * M + 12 * Real.pi) / (N * Real.log N)) := by
  classical
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hD : 0 ≤ (8 * C * M + 12 * Real.pi) / (N * Real.log N) := by positivity
  by_cases hs : (chiCubicHyperbolicPrimeSupport N M (p, r)).Nonempty
  swap
  · apply variation_le_of_norm_sum
    intro n u _ _
    have hempty : chiCubicHyperbolicPrimeSupport N M (p, r) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hs
    simpa only [hempty, Set.indicator_empty, Pi.zero_apply, sub_self, norm_zero,
      Finset.sum_const_zero] using hD
  let d := |(p : ℝ) - r|
  let R := (M : ℝ) * r / d
  let a := max N ((r : ℝ) - R)
  let b := min (2 * N) ((r : ℝ) + R)
  have hd1 : 1 ≤ d := prime_gap_one_le hne
  have hd : 0 < d := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsub : chiCubicHyperbolicPrimeSupport N M (p, r) ⊆ Set.Icc a b := by
    intro x hx
    rw [hyperbolic_support_eq M hne] at hx
    exact ⟨max_le hx.1.1.1.le hx.1.2.1, le_min hx.1.1.2 hx.1.2.2⟩
  have hab : a ≤ b := by
    obtain ⟨x, hx⟩ := hs
    exact (hsub hx).1.trans (hsub hx).2
  have hband : Set.Icc a b ⊆ Set.Icc N (2 * N) := fun x hx =>
    ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩
  have hlen : b - a ≤ 4 * (M : ℝ) * N / d := by
    have hh : b - a ≤ 2 * R := by
      have ha : (r : ℝ) - R ≤ a := le_max_right _ _
      have hb : b ≤ (r : ℝ) + R := min_le_right _ _
      linarith
    have hrN := (primeProfileBand_mem hN0.le hr).2.2
    have hR' : R ≤ (M : ℝ) * (2 * N) / d := by
      dsimp [R]
      gcongr
    have hh' := mul_le_mul_of_nonneg_left hR' (by norm_num : (0 : ℝ) ≤ 2)
    calc b - a ≤ 2 * R := hh
      _ ≤ 2 * ((M : ℝ) * (2 * N) / d) := hh'
      _ = _ := by ring
  have hlip0 : 0 ≤ C * (d + 1) / (N ^ 2 * Real.log N) := by positivity
  have hvar := variation_indicator_lipschitz hab
    (show 0 ≤ 2 * Real.pi / (N * Real.log N) by positivity) hlip0 (by norm_num : (0 : ℝ) ≤ 6)
    hsub (fun x hx => norm_chiCubicHyperbolicPrimeAmplitude_le hN hp hr (hband hx))
    (fun x hx y hy => hlip x (hband hx) y (hband hy))
    (variation_hyperbolic_support hN0.le M hne)
  apply hvar.trans
  apply ENNReal.ofReal_le_ofReal
  have hratio : (d + 1) / d ≤ 2 := (div_le_iff₀ hd).2 (by linarith)
  have hterm : C * (d + 1) / (N ^ 2 * Real.log N) * (b - a) ≤
      8 * C * M / (N * Real.log N) := by
    calc
      _ ≤ C * (d + 1) / (N ^ 2 * Real.log N) * (4 * (M : ℝ) * N / d) :=
        mul_le_mul_of_nonneg_left hlen hlip0
      _ = (4 * C * M / (N * Real.log N)) * ((d + 1) / d) := by field_simp
      _ ≤ (4 * C * M / (N * Real.log N)) * 2 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 8 * C * M / (N * Real.log N) + (2 * Real.pi / (N * Real.log N)) * 6 :=
      add_le_add hterm le_rfl
    _ = _ := by ring

private def hyperbolicActivePrimePairs (N : ℝ) (M : ℕ) : Finset (ℕ × ℕ) :=
  ((primeProfileBand N).product (primeProfileBand N)).filter fun pr =>
    pr.1 ≠ pr.2 ∧ |(pr.1 : ℝ) - pr.2| ≤ ((M : ℝ) + 1) * Real.sqrt N

private theorem hyperbolic_support_gap {N : ℝ} (hN : 0 < N) (M : ℕ)
    {p r : ℕ} (hr : r ∈ primeProfileBand N) {x : ℝ}
    (hx : x ∈ chiCubicHyperbolicPrimeSupport N M (p, r)) :
    |(p : ℝ) - r| ≤ ((M : ℝ) + 1) * Real.sqrt N := by
  have hs : |(p : ℝ) - r| ^ 2 ≤ (M : ℝ) * r := by
    have h := mul_le_mul_of_nonneg_left hx.2.1.le (abs_nonneg ((p : ℝ) - r))
    nlinarith [hx.2.2]
  have hrN := mul_le_mul_of_nonneg_left (primeProfileBand_mem hN.le hr).2.2 (Nat.cast_nonneg M)
  have hL : 0 ≤ ((M : ℝ) + 1) * Real.sqrt N := by positivity
  have hsqrt := Real.sq_sqrt hN.le
  have hsquare : 2 * (M : ℝ) * N ≤ (((M : ℝ) + 1) * Real.sqrt N) ^ 2 := by
    rw [mul_pow, hsqrt]
    nlinarith [mul_nonneg (sq_nonneg (M : ℝ)) hN.le]
  nlinarith [abs_nonneg ((p : ℝ) - r)]

private theorem hyperbolic_kernel_eq_active {N : ℝ} (hN : 0 < N) (M : ℕ) (x : ℝ) :
    chiCubicHyperbolicPrimeKernel N M x =
      ∑ pr ∈ hyperbolicActivePrimePairs N M,
        (chiCubicHyperbolicPrimeSupport N M pr).indicator (chiCubicHyperbolicPrimeAmplitude N pr) x := by
  classical
  unfold chiCubicHyperbolicPrimeKernel hyperbolicActivePrimePairs
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨p, r⟩ hpr
  have hr := (Finset.mem_product.1 hpr).2
  by_cases hne : p = r
  · simp [hne]
  by_cases hx : x ∈ chiCubicHyperbolicPrimeSupport N M (p, r)
  · simp [hne, hx, hyperbolic_support_gap hN M hr hx]
  · simp [hne, hx]

private theorem card_hyperbolicActivePrimePairs {N : ℝ} (hN : 4 ≤ N)
    (hlog : 1 ≤ Real.log N) (M : ℕ) :
    ((hyperbolicActivePrimePairs N M).card : ℝ) ≤
      28 * ((M : ℝ) + 1) * N * Real.sqrt N * Real.log N := by
  classical
  have hN0 : 0 < N := by linarith
  let L := ((M : ℝ) + 1) * Real.sqrt N
  let B := ⌊2 * N⌋₊
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hsub : hyperbolicActivePrimePairs N M ⊆ chiCubicHyperbolicIntegerPairs B (2 * L * N) 0 := by
    rintro ⟨p, r⟩ hpr
    obtain ⟨hmem, hne, hgap⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
    have hpB := Nat.le_floor (primeProfileBand_mem hN0.le hp).2.2
    have hrB := Nat.le_floor (primeProfileBand_mem hN0.le hr).2.2
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨Finset.mem_range.2 (by dsimp [B]; omega), Finset.mem_range.2 (by dsimp [B]; omega)⟩, hne, ?_⟩
    change |(p : ℝ) - r| * |0 - (r : ℝ)| ≤ 2 * L * N
    rw [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    calc
      _ ≤ L * (2 * N) :=
        mul_le_mul hgap (primeProfileBand_mem hN0.le hr).2.2 (Nat.cast_nonneg r) hL
      _ = _ := by ring
  have hcard : ((hyperbolicActivePrimePairs N M).card : ℝ) ≤
      4 * (2 * L * N) * (1 + Real.log B) + 2 * B :=
    (show ((hyperbolicActivePrimePairs N M).card : ℝ) ≤
        (chiCubicHyperbolicIntegerPairs B (2 * L * N) 0).card by
      exact_mod_cast Finset.card_le_card hsub).trans
        (card_chiCubicHyperbolicIntegerPairs B (by positivity) (by norm_num))
  have hB0 : (0 : ℝ) < B := by
    exact_mod_cast (Nat.floor_pos.2 (show 1 ≤ 2 * N by linarith))
  have hB : (B : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
  have hlogB : 1 + Real.log B ≤ 3 * Real.log N := by
    have h := Real.log_le_log hB0 hB
    rw [Real.log_mul (by norm_num) hN0.ne'] at h
    have htwo : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hN0.le, Real.sqrt_nonneg N]
  have hL1 : 1 ≤ L := by dsimp [L]; nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hcard' : ((hyperbolicActivePrimePairs N M).card : ℝ) ≤
      24 * L * N * Real.log N + 4 * N := by
    have hh := mul_le_mul_of_nonneg_left hlogB (show 0 ≤ 4 * (2 * L * N) by positivity)
    nlinarith
  have htail : 4 * N ≤ 4 * L * N * Real.log N := by
    have hh := mul_le_mul hL1 hlog (by norm_num : (0 : ℝ) ≤ 1) hL
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * N by positivity)
    nlinarith
  calc
    _ ≤ 24 * L * N * Real.log N + 4 * N := hcard'
    _ ≤ 24 * L * N * Real.log N + 4 * L * N * Real.log N := add_le_add le_rfl htail
    _ = _ := by dsimp [L]; ring

/-- The actual zero-extended kernel has globally bounded variation of order
`sqrt N`, uniformly over every sufficiently positive band. All sharp support
jumps are included; no regularity or cancellation hypothesis is imposed. -/
theorem exists_chiCubicHyperbolicPrimeKernel_variation (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 4 ≤ N → 1 ≤ Real.log N →
      BoundedVariationOn (chiCubicHyperbolicPrimeKernel N M) Set.univ ∧
      (eVariationOn (chiCubicHyperbolicPrimeKernel N M) Set.univ).toReal ≤ C * Real.sqrt N := by
  classical
  obtain ⟨C, hC, hLip⟩ := exists_chiCubicHyperbolicPrimeAmplitude_lipschitz
  let D := 8 * C * M + 12 * Real.pi
  let E := 28 * ((M : ℝ) + 1) * D
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E, hE, ?_⟩
  intro N hN hlog
  have hN0 : 0 < N := by linarith
  have hN1 : 1 < N := by linarith
  have hlog0 : 0 < Real.log N := by linarith
  let S := hyperbolicActivePrimePairs N M
  let f := fun pr : ℕ × ℕ => (chiCubicHyperbolicPrimeSupport N M pr).indicator
    (chiCubicHyperbolicPrimeAmplitude N pr)
  have hvar (pr : ℕ × ℕ) (hpr : pr ∈ S) :
      eVariationOn (f pr) Set.univ ≤ ENNReal.ofReal (D / (N * Real.log N)) := by
    have hmem := Finset.mem_filter.1 hpr
    have hpair := Finset.mem_product.1 hmem.1
    exact variation_hyperbolic_pair hN1 hC M hpair.1 hpair.2 hmem.2.1
      (hLip N hN1 hlog pr.1 hpair.1 pr.2 hpair.2)
  have htotal : eVariationOn (chiCubicHyperbolicPrimeKernel N M) Set.univ ≤
      ENNReal.ofReal (E * Real.sqrt N) := by
    apply variation_le_of_norm_sum
    intro n u hu hs
    calc
      _ ≤ ∑ i ∈ Finset.range n, ∑ pr ∈ S, ‖f pr (u (i + 1)) - f pr (u i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [hyperbolic_kernel_eq_active hN0 M, hyperbolic_kernel_eq_active hN0 M,
          ← Finset.sum_sub_distrib]
        exact norm_sum_le _ _
      _ = ∑ pr ∈ S, ∑ i ∈ Finset.range n, ‖f pr (u (i + 1)) - f pr (u i)‖ :=
        Finset.sum_comm
      _ ≤ ∑ _pr ∈ S, D / (N * Real.log N) := Finset.sum_le_sum fun pr hpr =>
        norm_sum_le_variation_bound (by positivity) (hvar pr hpr) n u hu hs
      _ = (S.card : ℝ) * (D / (N * Real.log N)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (28 * ((M : ℝ) + 1) * N * Real.sqrt N * Real.log N) * (D / (N * Real.log N)) :=
        mul_le_mul_of_nonneg_right (card_hyperbolicActivePrimePairs hN hlog M) (by positivity)
      _ = E * Real.sqrt N := by dsimp [E]; field_simp
  refine ⟨(htotal.trans_lt ENNReal.ofReal_lt_top).ne, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
  rwa [ENNReal.toReal_ofReal (show 0 ≤ E * Real.sqrt N by positivity)] at hh

/-- Unconditional eventual variation estimate for the actual signed prime kernel. -/
theorem chiCubicHyperbolicPrimeKernel_variation (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop,
      BoundedVariationOn (chiCubicHyperbolicPrimeKernel N M) Set.univ ∧
      (eVariationOn (chiCubicHyperbolicPrimeKernel N M) Set.univ).toReal ≤ C * Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_chiCubicHyperbolicPrimeKernel_variation M
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with N hN hlog
  exact h N hN hlog

/-- Freezing the actual nonoscillatory amplitude at the prime anchor loses no
gap factor: the original recentered phase is retained exactly. -/
theorem exists_chiCubicHyperbolicPrimeAmplitude_freeze :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 < N → 1 ≤ Real.log N →
      ∀ p ∈ primeProfileBand N, ∀ r ∈ primeProfileBand N,
      ∀ x ∈ Set.Icc N (2 * N),
      ‖chiCubicHyperbolicPrimeAmplitude N (p, r) x -
        chiCubicHyperbolicPrimeAmplitude N (p, r) r *
          bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r))‖ ≤
        C / (N ^ 2 * Real.log N) * |x - r| := by
  obtain ⟨B, hB, hF⟩ := exists_primeGaussianScaledLogProfile_lipschitz
  refine ⟨4 * Real.pi * B, by positivity, ?_⟩
  intro N hN hlog p hp r hr x hx
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := by linarith
  have hpN := (primeProfileBand_mem hN0.le hp).2
  have hrN := (primeProfileBand_mem hN0.le hr).2
  have hr0 : (0 : ℝ) < r := hN0.trans hrN.1
  have hrx : (r : ℝ) ∈ Set.Icc N (2 * N) := ⟨hrN.1.le, hrN.2⟩
  have hξ : (p : ℝ) / r ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hr0).2
      linarith [hpN.1, hrN.2]
    · apply (div_le_iff₀ hr0).2
      linarith [hpN.2, hrN.1]
  have hl : 1 / Real.log N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hL).2 hlog⟩
  have hscaled (z : ℝ) (hz : z ∈ Set.Icc N (2 * N)) :
      z / N ∈ Set.Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hN0).2 (by simpa using hz.1), (div_le_iff₀ hN0).2 hz.2⟩
  let g := fun z : ℝ => primeGaussianScaledLogProfile ((p : ℝ) / r) (1 / Real.log N) (z / N)
  let e := bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r))
  have hgd : ‖g x - g r‖ ≤ (2 * (B : ℝ) / N) * |x - r| := by
    have h := (hF _ hξ _ hl).2.dist_le_mul _ (hscaled x hx) _ (hscaled r hrx)
    rw [dist_eq_norm, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hN0] at h
    change ‖g x - g r‖ ≤ (2 * (B : ℝ)) * (|x - r| / N) at h
    convert h using 1; ring
  have her : bourgainOscillation
      (2 * Real.pi * (((p : ℝ) - r) * ((r : ℝ) - r) / r)) = 1 := by
    simp [bourgainOscillation]
  rw [hyperbolic_amplitude_factor hN hx, hyperbolic_amplitude_factor hN hrx,
    her, mul_one]
  change ‖hyperbolicAmplitudeCoefficient N p r * g x * e -
    hyperbolicAmplitudeCoefficient N p r * g r * e‖ ≤ _
  rw [show hyperbolicAmplitudeCoefficient N p r * g x * e -
      hyperbolicAmplitudeCoefficient N p r * g r * e =
        hyperbolicAmplitudeCoefficient N p r * (g x - g r) * e by ring,
    norm_mul, norm_mul, norm_bourgainOscillation, mul_one]
  calc
    _ ≤ (2 * Real.pi / (N * Real.log N)) * ((2 * (B : ℝ) / N) * |x - r|) :=
      mul_le_mul (hyperbolic_coefficient_norm hN hp hr) hgd (norm_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

end RHTower
end
