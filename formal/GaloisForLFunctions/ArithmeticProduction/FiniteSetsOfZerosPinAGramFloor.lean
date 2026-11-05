import GaloisForLFunctions.ArithmeticProduction.EveryOffLineZeroPinsAFloor

/-!
# Finite sets of zeros pin a Gram floor

The floor at one off-line zero extends to any finite set `Z` of off-line zeros, in the form of an interpolation problem in the Hardy space of `Re s > ½`.  With the Szegő kernel
`G(ρ, σ) = 1/(ρ + σ̄ − 1)` and the values `v(ρ) = (1 − ρ)/ρ²`, for every Dirichlet polynomial of any length and every vector `y`,

  `|Σ_ρ y(ρ) v(ρ)|² ≤ D · Σ_{ρ,σ} y(ρ) ȳ(σ) G(ρ, σ)`  (`mollifierDefect_gram_floor`).

So the defect is at least `v* G⁻¹ v`.  For one zero this is `(2β−1)|1−ρ|²/|ρ|⁴`.

**Floors add, up to interference** (`mollifierDefect_floor_sum`).  With `F = Σ_ρ (2β_ρ−1)|1−ρ|²/|ρ|⁴` and `y(ρ) = (2β_ρ−1) v̄(ρ)`,

  `F² ≤ D · (F + Off)`,

where `Off` is the off-diagonal part of the Gram form: `Off ≪ F` gives `D ≳ F`.  A single zero only bounds the defect by its own height; a family of off-line zeros bounds it by the sum over the family.

The mechanism is the half-line Cauchy–Schwarz of the single-zero floor, with test function `Σ_ρ x(ρ) e^{−(ρ−½)u}`, whose `L²(0,∞)` Gram matrix is the Szegő kernel.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticProduction

/-- The test function `Σ_ρ x(ρ) e^{−(ρ−½)u}`. -/
def gramTest (Z : Finset ℂ) (x : ℂ → ℂ) (u : ℝ) : ℂ :=
  ∑ ρ ∈ Z, x ρ * Complex.exp (-(ρ - 1 / 2) * u)

/-- The Szegő form `Σ_{ρ,σ} x(ρ) x̄(σ) / (ρ + σ̄ − 1)`. -/
def gramForm (Z : Finset ℂ) (x : ℂ → ℂ) : ℂ :=
  ∑ ρ ∈ Z, ∑ σ ∈ Z, x ρ * conj (x σ) / (ρ + conj σ - 1)

private theorem normSq_exp_eq (ρ : ℂ) (u : ℝ) :
    ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2 = Real.exp (-(2 * ρ.re - 1) * u) := by
  have hre : (-(ρ - 1 / 2) * (u : ℂ)).re = -(ρ.re - 1 / 2) * u := by
    simp [Complex.mul_re]
  rw [Complex.norm_exp, ← Real.exp_nat_mul, hre]
  congr 1
  push_cast
  ring

private theorem integrableOn_norm_sq_exp {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    Integrable (fun u : ℝ => ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2) (volume.restrict (Ioi 0)) := by
  simp_rw [normSq_exp_eq]
  exact exp_neg_integrableOn_Ioi 0 (by linarith)

private theorem integrableOn_defectPull_mul_exp {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) :
    Integrable (fun u : ℝ => defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u))
      (volume.restrict (Ioi 0)) := by
  have hG := (integrable_norm_sq_defectPull hS a).integrableOn (s := Ioi (0 : ℝ))
  have hE := integrableOn_norm_sq_exp hρ
  refine Integrable.mono' (hG.add hE)
    (((integrable_defectPull hS a).aestronglyMeasurable.restrict).mul
      (Continuous.aestronglyMeasurable (by fun_prop))) (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  show ‖defectPull S a u‖ * ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ≤
    ‖defectPull S a u‖ ^ 2 + ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2
  nlinarith [sq_nonneg (‖defectPull S a u‖ - ‖Complex.exp (-(ρ - 1 / 2) * u)‖),
    sq_nonneg (‖defectPull S a u‖ + ‖Complex.exp (-(ρ - 1 / 2) * u)‖)]

/-- The pairing of the sawtooth pullback with the test function is determined at the zeros. -/
theorem integral_Ioi_defectPull_mul_gramTest {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0) (x : ℂ → ℂ) :
    ∫ u in Ioi (0 : ℝ), defectPull S a u * gramTest Z x u =
      ∑ ρ ∈ Z, x ρ * (1 / ρ - valueAtOne S a / (1 - ρ)) := by
  have hexpand : ∀ u : ℝ, defectPull S a u * gramTest Z x u =
      ∑ ρ ∈ Z, x ρ * (defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u)) := by
    intro u
    unfold gramTest
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ fun ρ hρ =>
    (integrableOn_defectPull_mul_exp hS a (hZ ρ hρ).1).const_mul _]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [integral_const_mul, integral_Ioi_defectPull_mul_cexp hS a (hZ ρ hρ).1 (hZ ρ hρ).2.1 (hZ ρ hρ).2.2]

private theorem gram_den_re_pos {ρ σ : ℂ} (hρ : 1 / 2 < ρ.re) (hσ : 1 / 2 < σ.re) :
    0 < (ρ + conj σ - 1).re := by
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
  linarith

/-- `‖g‖²` in terms of the exponentials. -/
private theorem ofReal_norm_sq_gramTest (Z : Finset ℂ) (x : ℂ → ℂ) (u : ℝ) :
    ((‖gramTest Z x u‖ ^ 2 : ℝ) : ℂ) =
      ∑ ρ ∈ Z, ∑ σ ∈ Z, x ρ * conj (x σ) * Complex.exp (-(ρ + conj σ - 1) * u) := by
  have h1 : ((‖gramTest Z x u‖ ^ 2 : ℝ) : ℂ) = gramTest Z x u * conj (gramTest Z x u) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1]
  unfold gramTest
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have h2 : conj (-(σ - 1 / 2) * (u : ℂ)) = -(conj σ - 1 / 2) * (u : ℂ) := by
    simp only [map_mul, map_neg, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  rw [h2]
  have h3 : -(ρ + conj σ - 1) * (u : ℂ) = -(ρ - 1 / 2) * (u : ℂ) + -(conj σ - 1 / 2) * (u : ℂ) := by
    ring
  rw [h3, Complex.exp_add]
  ring

private theorem integrableOn_exp_gram {ρ σ : ℂ} (hρ : 1 / 2 < ρ.re) (hσ : 1 / 2 < σ.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(ρ + conj σ - 1) * u)) (Ioi 0) := by
  refine integrableOn_exp_mul_complex_Ioi (a := -(ρ + conj σ - 1)) ?_ 0
  have h := gram_den_re_pos hρ hσ
  simpa using h

/-- The test function is square integrable, with the Szegő form as its norm. -/
theorem integrable_and_integral_norm_sq_gramTest {Z : Finset ℂ} (hZ : ∀ ρ ∈ Z, 1 / 2 < ρ.re) (x : ℂ → ℂ) :
    Integrable (fun u : ℝ => ‖gramTest Z x u‖ ^ 2) (volume.restrict (Ioi 0)) ∧
      ∫ u in Ioi (0 : ℝ), ‖gramTest Z x u‖ ^ 2 = (gramForm Z x).re := by
  have hC : Integrable (fun u : ℝ => ((‖gramTest Z x u‖ ^ 2 : ℝ) : ℂ)) (volume.restrict (Ioi 0)) := by
    simp_rw [ofReal_norm_sq_gramTest]
    refine integrable_finsetSum _ fun ρ hρ => integrable_finsetSum _ fun σ hσ => ?_
    exact (integrableOn_exp_gram (hZ ρ hρ) (hZ σ hσ)).const_mul _
  refine ⟨hC.re.congr (Filter.Eventually.of_forall fun u => Complex.ofReal_re _), ?_⟩
  have hval : ∫ u in Ioi (0 : ℝ), ((‖gramTest Z x u‖ ^ 2 : ℝ) : ℂ) = gramForm Z x := by
    simp_rw [ofReal_norm_sq_gramTest]
    rw [integral_finsetSum _ fun ρ hρ => integrable_finsetSum _ fun σ hσ =>
      (integrableOn_exp_gram (hZ ρ hρ) (hZ σ hσ)).const_mul _]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [integral_finsetSum _ fun σ hσ => (integrableOn_exp_gram (hZ ρ hρ) (hZ σ hσ)).const_mul _]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [integral_const_mul]
    have hre : (-(ρ + conj σ - 1)).re < 0 := by
      have h := gram_den_re_pos (hZ ρ hρ) (hZ σ hσ)
      simpa using h
    rw [integral_exp_mul_complex_Ioi hre 0]
    have hne : ρ + conj σ - 1 ≠ 0 := by
      intro h0
      have h := gram_den_re_pos (hZ ρ hρ) (hZ σ hσ)
      rw [h0, Complex.zero_re] at h
      exact lt_irrefl _ h
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
  have h1 := congrArg Complex.re hval
  rw [integral_complex_ofReal, Complex.ofReal_re] at h1
  exact h1

/-- The mass of the sawtooth pullback splits at `u = 0`, with `D(1)²` on the left half-line. -/
private theorem valueAtOne_sq_add_integral_Ioi_le {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    valueAtOne S a ^ 2 + ∫ u in Ioi (0 : ℝ), ‖defectPull S a u‖ ^ 2 ≤ mollifierDefect S a := by
  have hG := integrable_norm_sq_defectPull hS a
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact lt_asymm (show u < 0 from hu) (show 0 < u from hu')
  have hsub : ∫ u in Iio (0 : ℝ) ∪ Ioi 0, ‖defectPull S a u‖ ^ 2 ≤ mollifierDefect S a :=
    setIntegral_le_integral hG (Filter.Eventually.of_forall fun u => by positivity)
  rw [setIntegral_union hdisj measurableSet_Ioi hG.integrableOn hG.integrableOn] at hsub
  have hneg : ∫ u in Iio (0 : ℝ), ‖defectPull S a u‖ ^ 2 = valueAtOne S a ^ 2 := by
    have hpt : ∀ u ∈ Iio (0 : ℝ), ‖defectPull S a u‖ ^ 2 = valueAtOne S a ^ 2 * Real.exp u := by
      intro u hu
      rw [defectPull_of_neg hS a hu, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
        ← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (u / 2) = u := by
        push_cast
        ring
      rw [this]
      ring
    rw [setIntegral_congr_fun measurableSet_Iio hpt, integral_const_mul,
      ← integral_Iic_eq_integral_Iio, integral_exp_Iic_zero, mul_one]
  rw [hneg] at hsub
  exact hsub

/-- Cauchy–Schwarz in the plane. -/
private theorem plane_cauchy_schwarz {a b c E Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hE : 0 ≤ E)
    (hQ : 0 ≤ Q) (h : a ^ 2 ≤ E * Q) : (a + b * c) ^ 2 ≤ (E + b ^ 2) * (Q + c ^ 2) := by
  have hP : 0 ≤ E * c ^ 2 + b ^ 2 * Q := by positivity
  have hR : 0 ≤ 2 * (a * (b * c)) := by positivity
  have hsq : (2 * (a * (b * c))) ^ 2 ≤ (E * c ^ 2 + b ^ 2 * Q) ^ 2 := by
    have h1 : (E * c ^ 2 + b ^ 2 * Q) ^ 2 = 4 * (E * Q) * (b * c) ^ 2 + (E * c ^ 2 - b ^ 2 * Q) ^ 2 := by
      ring
    have h2 : (2 * (a * (b * c))) ^ 2 = 4 * a ^ 2 * (b * c) ^ 2 := by ring
    rw [h1, h2]
    have h3 : 4 * a ^ 2 * (b * c) ^ 2 ≤ 4 * (E * Q) * (b * c) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [sq_nonneg (E * c ^ 2 - b ^ 2 * Q)]
  have hle := (sq_le_sq₀ hR hP).mp hsq
  have hexp : (E + b ^ 2) * (Q + c ^ 2) - (a + b * c) ^ 2 =
      (E * Q - a ^ 2) + (E * c ^ 2 + b ^ 2 * Q - 2 * (a * (b * c))) := by ring
  linarith

/-- **The floor with `D(1)` eliminated.** -/
theorem norm_sq_sum_le_defect_mul {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0) (x : ℂ → ℂ) :
    ‖∑ ρ ∈ Z, x ρ / ρ‖ ^ 2 ≤
      mollifierDefect S a * ((gramForm Z x).re + ‖∑ ρ ∈ Z, x ρ / (1 - ρ)‖ ^ 2) := by
  obtain ⟨hgi, hgv⟩ := integrable_and_integral_norm_sq_gramTest (fun ρ hρ => (hZ ρ hρ).1) x
  have hGi := (integrable_norm_sq_defectPull hS a).integrableOn (s := Ioi (0 : ℝ))
  have hgm : AEStronglyMeasurable (gramTest Z x) (volume.restrict (Ioi 0)) := by
    refine Continuous.aestronglyMeasurable ?_
    unfold gramTest
    fun_prop
  have hCS := norm_sq_integral_mul_le (μ := volume.restrict (Ioi (0 : ℝ))) (f := defectPull S a)
    (g := gramTest Z x) (integrable_defectPull hS a).aestronglyMeasurable.restrict hgm hGi hgi
  rw [integral_Ioi_defectPull_mul_gramTest hS a hZ x, hgv] at hCS
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = valueAtOne S a := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∫ u in Ioi (0 : ℝ), ‖defectPull S a u‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (gramForm Z x).re := ⟨_, rfl⟩
  rw [← hE, ← hQ] at hCS
  rw [← hQ]
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact integral_nonneg fun u => by positivity
  have hQ0 : 0 ≤ Q := by
    rw [hQ, ← hgv]
    exact integral_nonneg fun u => by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = ∑ ρ ∈ Z, x ρ / ρ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = ∑ ρ ∈ Z, x ρ / (1 - ρ) := ⟨_, rfl⟩
  have hsum : ∑ ρ ∈ Z, x ρ * (1 / ρ - valueAtOne S a / (1 - ρ)) = A - (w : ℂ) * B := by
    rw [hA, hB, hw, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  rw [hsum] at hCS
  rw [← hA, ← hB]
  have htri : ‖A‖ ≤ ‖A - (w : ℂ) * B‖ + |w| * ‖B‖ := by
    have h1 := norm_add_le (A - (w : ℂ) * B) ((w : ℂ) * B)
    rw [sub_add_cancel, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  have hplane := plane_cauchy_schwarz (norm_nonneg (A - (w : ℂ) * B)) (abs_nonneg w) (norm_nonneg B)
    hE0 hQ0 hCS
  have hD : E + |w| ^ 2 ≤ mollifierDefect S a := by
    have h1 := valueAtOne_sq_add_integral_Ioi_le hS a
    rw [← hw, ← hE] at h1
    rw [sq_abs]
    linarith
  calc ‖A‖ ^ 2 ≤ (‖A - (w : ℂ) * B‖ + |w| * ‖B‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (E + |w| ^ 2) * (Q + ‖B‖ ^ 2) := hplane
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)

/-- **The Gram floor.**  The defect dominates the interpolation form of the values `(1 − ρ)/ρ²` against the Szegő kernel. -/
theorem mollifierDefect_gram_floor {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0) (y : ℂ → ℂ) :
    ‖∑ ρ ∈ Z, y ρ * ((1 - ρ) / ρ ^ 2)‖ ^ 2 ≤ mollifierDefect S a * (gramForm Z y).re := by
  have hbase := norm_sq_sum_le_defect_mul hS a hZ (fun ρ => y ρ * (1 - ρ) / ρ)
  have hρ0 : ∀ ρ ∈ Z, ρ ≠ 0 := fun ρ hρ h => by
    have := (hZ ρ hρ).1
    rw [h, Complex.zero_re] at this
    norm_num at this
  have hρ1 : ∀ ρ ∈ Z, 1 - ρ ≠ 0 := fun ρ hρ h => by
    have h1 := congrArg Complex.re h
    have h2 := (hZ ρ hρ).2.1
    simp at h1
    linarith
  have hA : ∑ ρ ∈ Z, (fun ρ => y ρ * (1 - ρ) / ρ) ρ / ρ = ∑ ρ ∈ Z, y ρ * ((1 - ρ) / ρ ^ 2) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have := hρ0 ρ hρ
    field_simp
  have hB : ∑ ρ ∈ Z, (fun ρ => y ρ * (1 - ρ) / ρ) ρ / (1 - ρ) = ∑ ρ ∈ Z, y ρ / ρ := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have h1 := hρ0 ρ hρ
    have h2 := hρ1 ρ hρ
    field_simp
  rw [hA, hB] at hbase
  refine hbase.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) (integral_nonneg fun u => by positivity))
  -- the sum of the two forms is the form of `y`
  have hnorm : ((‖∑ ρ ∈ Z, y ρ / ρ‖ ^ 2 : ℝ) : ℂ) =
      ∑ ρ ∈ Z, ∑ σ ∈ Z, (y ρ / ρ) * conj (y σ / σ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  have hre : ‖∑ ρ ∈ Z, y ρ / ρ‖ ^ 2 = (∑ ρ ∈ Z, ∑ σ ∈ Z, (y ρ / ρ) * conj (y σ / σ)).re := by
    rw [← hnorm, Complex.ofReal_re]
  rw [hre, ← Complex.add_re]
  congr 1
  unfold gramForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h1 := hρ0 ρ hρ
  have h2 := hρ0 σ hσ
  have h3 := hρ1 ρ hρ
  have h4 : conj σ ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact h2
  have h5 : 1 - conj σ ≠ 0 := by
    have h6 := hρ1 σ hσ
    intro h7
    apply h6
    have h8 := congrArg conj h7
    simpa using h8
  have h6 : ρ + conj σ - 1 ≠ 0 := by
    intro h0
    have h := gram_den_re_pos (hZ ρ hρ).1 (hZ σ hσ).1
    rw [h0, Complex.zero_re] at h
    exact lt_irrefl _ h
  simp only [map_div₀, map_mul, map_sub, map_one]
  field_simp
  ring

/-- **One zero** recovers the single floor. -/
theorem mollifierDefect_gram_floor_singleton {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {ρ : ℂ}
    (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ‖(1 - ρ) / ρ ^ 2‖ ^ 2 * (2 * ρ.re - 1) ≤ mollifierDefect S a := by
  have h := mollifierDefect_gram_floor hS a (Z := {ρ}) (fun r hr => by
    rw [Finset.mem_singleton] at hr
    subst hr
    exact ⟨hρ0, hρ1, hz⟩) (fun _ => 1)
  have hA : 0 < 2 * ρ.re - 1 := by linarith
  have hval : (gramForm {ρ} (fun _ => 1)).re = (2 * ρ.re - 1)⁻¹ := by
    unfold gramForm
    simp only [Finset.sum_singleton, map_one, mul_one]
    have h1 : ρ + conj ρ - 1 = ((2 * ρ.re - 1 : ℝ) : ℂ) := by
      rw [Complex.add_conj]
      push_cast
      ring
    rw [h1, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re, one_div]
  rw [hval] at h
  simp only [Finset.sum_singleton, one_mul] at h
  calc ‖(1 - ρ) / ρ ^ 2‖ ^ 2 * (2 * ρ.re - 1)
      ≤ mollifierDefect S a * (2 * ρ.re - 1)⁻¹ * (2 * ρ.re - 1) :=
        mul_le_mul_of_nonneg_right h hA.le
    _ = _ := by
        field_simp

/-- **Floors add, up to interference.**  With `F = Σ_ρ (2β_ρ−1)|v(ρ)|²` and `Off` the off-diagonal of the Gram form at `y(ρ) = (2β_ρ−1) v̄(ρ)`: `F² ≤ D (F + Off)`. -/
theorem mollifierDefect_floor_sum {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0) :
    (∑ ρ ∈ Z, (2 * ρ.re - 1) * ‖(1 - ρ) / ρ ^ 2‖ ^ 2) ^ 2 ≤
      mollifierDefect S a * ((∑ ρ ∈ Z, (2 * ρ.re - 1) * ‖(1 - ρ) / ρ ^ 2‖ ^ 2) +
        (∑ ρ ∈ Z, ∑ σ ∈ Z.erase ρ,
          (((2 * ρ.re - 1 : ℝ) : ℂ) * conj ((1 - ρ) / ρ ^ 2)) *
            conj (((2 * σ.re - 1 : ℝ) : ℂ) * conj ((1 - σ) / σ ^ 2)) / (ρ + conj σ - 1)).re) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : ℂ → ℂ, v = fun ρ => (1 - ρ) / ρ ^ 2 := ⟨_, rfl⟩
  have h := mollifierDefect_gram_floor hS a hZ (fun ρ => ((2 * ρ.re - 1 : ℝ) : ℂ) * conj (v ρ))
  have hnum : ∑ ρ ∈ Z, ((2 * ρ.re - 1 : ℝ) : ℂ) * conj (v ρ) * ((1 - ρ) / ρ ^ 2) =
      ((∑ ρ ∈ Z, (2 * ρ.re - 1) * ‖(1 - ρ) / ρ ^ 2‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have h1 : v ρ = (1 - ρ) / ρ ^ 2 := by rw [hv]
    rw [h1, Complex.ofReal_mul, mul_assoc, mul_comm (conj _), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  have hF0 : 0 ≤ ∑ ρ ∈ Z, (2 * ρ.re - 1) * ‖(1 - ρ) / ρ ^ 2‖ ^ 2 :=
    Finset.sum_nonneg fun ρ hρ => mul_nonneg (by linarith [(hZ ρ hρ).1]) (by positivity)
  rw [hnum, Complex.norm_real, Real.norm_of_nonneg hF0] at h
  refine h.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) (integral_nonneg fun u => by positivity))
  unfold gramForm
  have hsplit : ∀ ρ ∈ Z, ∑ σ ∈ Z, (((2 * ρ.re - 1 : ℝ) : ℂ) * conj (v ρ)) *
        conj (((2 * σ.re - 1 : ℝ) : ℂ) * conj (v σ)) / (ρ + conj σ - 1) =
      (((2 * ρ.re - 1) * ‖(1 - ρ) / ρ ^ 2‖ ^ 2 : ℝ) : ℂ) +
        ∑ σ ∈ Z.erase ρ, (((2 * ρ.re - 1 : ℝ) : ℂ) * conj (v ρ)) *
          conj (((2 * σ.re - 1 : ℝ) : ℂ) * conj (v σ)) / (ρ + conj σ - 1) := by
    intro ρ hρ
    rw [← Finset.add_sum_erase Z _ hρ]
    congr 1
    have hA : ((2 * ρ.re - 1 : ℝ) : ℂ) ≠ 0 := by
      have := (hZ ρ hρ).1
      exact_mod_cast (by linarith : (0 : ℝ) < 2 * ρ.re - 1).ne'
    have h1 : ρ + conj ρ - 1 = ((2 * ρ.re - 1 : ℝ) : ℂ) := by
      rw [Complex.add_conj]
      push_cast
      ring
    have h2 : v ρ = (1 - ρ) / ρ ^ 2 := by rw [hv]
    rw [h1, map_mul, Complex.conj_conj, Complex.conj_ofReal, h2, Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Complex.add_re, ← Complex.ofReal_sum,
    Complex.ofReal_re]
  subst hv
  rfl

end GaloisForLFunctions.ArithmeticProduction
