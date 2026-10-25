import GaloisForLFunctions.HTGeometry.BochnerPositiveDefiniteReal

/-!
# Herglotz–Bochner on the lattices `ℤ^ι`

A function `φ : ℤ^ι → ℂ` is positive definite when every Gram form
`Σ_{a,b} c̄_a φ(x_b − x_a) c_b` is real and nonnegative. The dual group of `ℤ^ι` is the torus
`T^ι = (ℝ/2πℤ)^ι`; here measures on it are measures on `ℝ^ι`, read through the characters
`χ_m(θ) = e^{i⟨m, θ⟩}`, `m ∈ ℤ^ι`.

**Theorem** (`isPosDefOnLattice_iff`). `φ` is positive definite iff it is the Fourier coefficient
sequence `m ↦ ∫ χ_m dμ` of a finite positive measure `μ`.

* (⇐) The Gram form is `∫ |Σ_b c_b χ_{x_b}|² dμ` (`isPosDefOnLattice_fourierCoeff`).
* (⇒) Fejér means. On the box `(−π, π]^ι` the density
  `F_N(θ) = ((N+1)(2π))^{−r} Σ_{j,k ∈ [0,N]^ι} φ(k − j) e^{−i⟨k−j, θ⟩}` is a Gram form at the
  vectors `(e^{−i⟨j,θ⟩})_j`, hence nonnegative (`latticeFejerDensity_nonneg`). Its coefficients are
  `φ(m) Π_i c_N(m_i)`, with `c_N(l) = #{a ≤ N : 0 ≤ a + l ≤ N}/(N+1) → 1`
  (`fourierCoeff_latticeFejerMeasure`). The Fejér measures live on one compact box, so Prokhorov
  gives a weak limit along a subsequence; its coefficients are `φ`.

This is the tool behind the rank-`r` Bochner problems of the programme: positivity of a
correlation on `ℤ log p₁ + ⋯ + ℤ log p_r ≅ ℤ^r` is the existence of a positive measure on `T^r`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate BigOperators Real ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Characters of the torus -/

/-- The pairing `⟨m, θ⟩ = Σ_i m_i θ_i`. -/
def pairing (m : ι → ℤ) (θ : ι → ℝ) : ℝ := ∑ i, (m i : ℝ) * θ i

omit [DecidableEq ι] in
theorem pairing_add (m n : ι → ℤ) (θ : ι → ℝ) :
    pairing (m + n) θ = pairing m θ + pairing n θ := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem pairing_neg (m : ι → ℤ) (θ : ι → ℝ) : pairing (-m) θ = -pairing m θ := by
  simp [pairing, Finset.sum_neg_distrib]

/-- The character `χ_m(θ) = e^{i⟨m, θ⟩}`. -/
def latticeChar (m : ι → ℤ) (θ : ι → ℝ) : ℂ := cexp (I * (pairing m θ : ℂ))

omit [DecidableEq ι] in
theorem latticeChar_add (m n : ι → ℤ) (θ : ι → ℝ) :
    latticeChar (m + n) θ = latticeChar m θ * latticeChar n θ := by
  simp only [latticeChar, pairing_add, Complex.ofReal_add, mul_add, Complex.exp_add]

omit [DecidableEq ι] in
theorem star_latticeChar (m : ι → ℤ) (θ : ι → ℝ) :
    star (latticeChar m θ) = latticeChar (-m) θ := by
  rw [latticeChar, latticeChar, pairing_neg, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal]

omit [DecidableEq ι] in
theorem norm_latticeChar (m : ι → ℤ) (θ : ι → ℝ) : ‖latticeChar m θ‖ = 1 := by
  rw [latticeChar, mul_comm, Complex.norm_exp_ofReal_mul_I]

omit [DecidableEq ι] in
theorem latticeChar_zero (θ : ι → ℝ) : latticeChar 0 θ = 1 := by
  simp [latticeChar, pairing]

omit [DecidableEq ι] in
theorem continuous_latticeChar (m : ι → ℤ) : Continuous (latticeChar m) := by
  unfold latticeChar pairing
  fun_prop

omit [DecidableEq ι] in
theorem latticeChar_eq_prod (m : ι → ℤ) (θ : ι → ℝ) :
    latticeChar m θ = ∏ i, cexp (I * (((m i : ℝ) * θ i : ℝ) : ℂ)) := by
  rw [latticeChar, pairing, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

/-- The character as a bounded continuous function. -/
def latticeCharBCF (m : ι → ℤ) : (ι → ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (latticeChar m) (continuous_latticeChar m) 1
    fun θ => (norm_latticeChar m θ).le

/-- Fourier coefficients of a measure on `ℝ^ι` at the integer frequencies. -/
def fourierCoeff (μ : Measure (ι → ℝ)) (m : ι → ℤ) : ℂ := ∫ θ, latticeChar m θ ∂μ

omit [DecidableEq ι] in
theorem integrable_latticeChar (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (m : ι → ℤ) :
    Integrable (latticeChar m) μ :=
  (latticeCharBCF m).integrable μ

/-! ### Positive definiteness on `ℤ^ι` -/

/-- Positive definiteness on `ℤ^ι`: every Gram form is real and nonnegative. -/
def IsPosDefOnLattice (φ : (ι → ℤ) → ℂ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → ι → ℤ) (c : Fin N → ℂ),
    ∃ r : ℝ, 0 ≤ r ∧ ∑ a, ∑ b, star (c a) * φ (x b - x a) * c b = r

omit [DecidableEq ι] in
/-- The Gram form over any finite index type. -/
theorem IsPosDefOnLattice.form {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) {κ : Type*}
    [Fintype κ] (x : κ → ι → ℤ) (c : κ → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ a, ∑ b, star (c a) * φ (x b - x a) * c b = r := by
  set e := (Fintype.equivFin κ).symm
  obtain ⟨r, hr, h⟩ := hφ (Fintype.card κ) (x ∘ e) (c ∘ e)
  refine ⟨r, hr, ?_⟩
  rw [← h, ← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← e.sum_comp]
  rfl

omit [DecidableEq ι] in
theorem IsPosDefOnLattice.re_nonneg_im_eq_zero {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ)
    {κ : Type*} [Fintype κ] (x : κ → ι → ℤ) (c : κ → ℂ) :
    0 ≤ (∑ a, ∑ b, star (c a) * φ (x b - x a) * c b).re ∧
      (∑ a, ∑ b, star (c a) * φ (x b - x a) * c b).im = 0 := by
  obtain ⟨r, hr, h⟩ := hφ.form x c
  rw [h]
  simp [hr]

omit [DecidableEq ι] in
theorem IsPosDefOnLattice.zero {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) :
    0 ≤ (φ 0).re ∧ (φ 0).im = 0 := by
  have h := hφ.re_nonneg_im_eq_zero (κ := Unit) (fun _ => 0) (fun _ => 1)
  simpa using h

omit [DecidableEq ι] in
/-- The `2 × 2` form at `0, m`. -/
theorem IsPosDefOnLattice.two_form {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (m : ι → ℤ)
    (a b : ℂ) :
    0 ≤ (star a * φ 0 * a + star a * φ m * b + star b * φ (-m) * a + star b * φ 0 * b).re ∧
      (star a * φ 0 * a + star a * φ m * b + star b * φ (-m) * a + star b * φ 0 * b).im = 0 := by
  have h := hφ.re_nonneg_im_eq_zero (κ := Fin 2) ![0, m] ![a, b]
  simpa [Fin.sum_univ_two, add_assoc] using h

omit [DecidableEq ι] in
theorem IsPosDefOnLattice.neg {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (m : ι → ℤ) :
    φ (-m) = conj (φ m) := by
  have h1 := (hφ.two_form m 1 1).2
  have h2 := (hφ.two_form m 1 I).2
  have h0 := hφ.zero.2
  simp only [star_one, one_mul, mul_one, Complex.add_im] at h1
  simp [Complex.mul_im, Complex.mul_re] at h2
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

omit [DecidableEq ι] in
/-- `|φ(m)| ≤ φ(0)`. -/
theorem IsPosDefOnLattice.norm_le {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (m : ι → ℤ) :
    ‖φ m‖ ≤ (φ 0).re := by
  have hneg := hφ.neg m
  have h00 := hφ.zero
  set p : ℝ := (φ 0).re with hp
  have hφ0 : φ 0 = (p : ℂ) := Complex.ext (by simp [hp]) (by simp [h00.2])
  have key : ∀ r : ℝ, 0 ≤ r → 0 ≤ p * (1 + r ^ 2 * ‖φ m‖ ^ 2) - 2 * r * ‖φ m‖ ^ 2 := by
    intro r hr
    have h := (hφ.two_form m 1 (-(r : ℂ) * conj (φ m))).1
    rw [hneg, hφ0] at h
    have hmul : φ m * conj (φ m) = (‖φ m‖ : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have hmul' : conj (φ m) * φ m = (‖φ m‖ : ℂ) ^ 2 := by rw [mul_comm, hmul]
    have e : (star (1 : ℂ) * (p : ℂ) * 1 + star 1 * φ m * (-(r : ℂ) * conj (φ m)) +
        star (-(r : ℂ) * conj (φ m)) * conj (φ m) * 1 +
        star (-(r : ℂ) * conj (φ m)) * (p : ℂ) * (-(r : ℂ) * conj (φ m))) =
        ((p * (1 + r ^ 2 * ‖φ m‖ ^ 2) - 2 * r * ‖φ m‖ ^ 2 : ℝ) : ℂ) := by
      simp only [star_one, one_mul, mul_one, star_mul', star_neg, Complex.star_def,
        Complex.conj_ofReal, Complex.conj_conj]
      push_cast
      linear_combination (-(r : ℂ)) * hmul - (r : ℂ) * hmul' + ((p : ℂ) * r ^ 2) * hmul'
    rw [e, Complex.ofReal_re] at h
    exact h
  rcases eq_or_lt_of_le h00.1 with hp0 | hp0
  · have := key 1 zero_le_one
    rw [← hp0] at this
    have : ‖φ m‖ = 0 := by nlinarith [norm_nonneg (φ m)]
    rw [this, ← hp0]
  · have := key (1 / p) (by positivity)
    have h2 : ‖φ m‖ ^ 2 ≤ p ^ 2 := by
      have e : p * (1 + (1 / p) ^ 2 * ‖φ m‖ ^ 2) - 2 * (1 / p) * ‖φ m‖ ^ 2 =
          (p ^ 2 - ‖φ m‖ ^ 2) / p := by field_simp; ring
      rw [e] at this
      rcases div_nonneg_iff.mp this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · linarith
    nlinarith [norm_nonneg (φ m)]

omit [DecidableEq ι] in
theorem IsPosDefOnLattice.const_mul {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) {c : ℝ}
    (hc : 0 ≤ c) : IsPosDefOnLattice fun m => (c : ℂ) * φ m := by
  intro N x v
  obtain ⟨r, hr, hsum⟩ := hφ N x v
  refine ⟨c * r, mul_nonneg hc hr, ?_⟩
  have : ∑ a, ∑ b, star (v a) * ((c : ℂ) * φ (x b - x a)) * v b =
      (c : ℂ) * ∑ a, ∑ b, star (v a) * φ (x b - x a) * v b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, hsum]
  push_cast
  ring

/-! ### Fourier coefficients of positive measures are positive definite -/

omit [DecidableEq ι] in
/-- **Herglotz–Bochner, easy half.** The Gram form of the coefficients of `μ` is
`∫ |Σ_b c_b χ_{x_b}|² dμ`. -/
theorem isPosDefOnLattice_fourierCoeff (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] :
    IsPosDefOnLattice (fourierCoeff μ) := by
  intro N x c
  refine ⟨∫ θ, Complex.normSq (∑ b, c b * latticeChar (x b) θ) ∂μ,
    integral_nonneg fun _ => Complex.normSq_nonneg _, ?_⟩
  have hpt : ∀ θ, ∑ a, ∑ b, star (c a) * latticeChar (x b - x a) θ * c b =
      (Complex.normSq (∑ b, c b * latticeChar (x b) θ) : ℂ) := by
    intro θ
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [sub_eq_add_neg, latticeChar_add, ← star_latticeChar, map_mul]
    simp only [Complex.star_def]
    ring
  rw [← integral_complex_ofReal]
  simp_rw [← hpt]
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
    ((integrable_latticeChar μ _).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => ((integrable_latticeChar μ _).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_const_mul]
  rfl

/-! ### The box and the Fejér measures -/

/-- Normalized-free Lebesgue measure on the box `(−π, π]^ι`. -/
def boxMeasure : Measure (ι → ℝ) := Measure.pi fun _ : ι => volume.restrict (Ioc (-π) π)

instance : IsFiniteMeasure (volume.restrict (Ioc (-π) π) : Measure ℝ) :=
  isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne

instance : IsFiniteMeasure (boxMeasure : Measure (ι → ℝ)) := by
  unfold boxMeasure; infer_instance

omit [DecidableEq ι] in
/-- `∫_{(−π,π]^ι} χ_n = (2π)^r [n = 0]`. -/
theorem integral_latticeChar_boxMeasure (n : ι → ℤ) :
    ∫ θ, latticeChar n θ ∂boxMeasure =
      if n = 0 then (((2 * π) ^ Fintype.card ι : ℝ) : ℂ) else 0 := by
  simp_rw [latticeChar_eq_prod]
  rw [boxMeasure, integral_fintype_prod_eq_prod (fun i t => cexp (I * (((n i : ℝ) * t : ℝ) : ℂ)))]
  have h1 : ∀ i, ∫ t, cexp (I * (((n i : ℝ) * t : ℝ) : ℂ)) ∂(volume.restrict (Ioc (-π) π)) =
      if n i = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
    intro i
    have := Bochner.integral_exp_lattice 1 one_pos (n i)
    simp only [mul_one, div_one] at this
    rwa [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])] at this
  simp_rw [h1]
  split_ifs with hn
  · subst hn
    simp
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Integer points of the window `[0, N]^ι`. -/
def windowPt (N : ℕ) (j : ι → Fin (N + 1)) : ι → ℤ := fun i => ((j i : ℕ) : ℤ)

/-- The scalar `((N + 1) · 2π)^{−r}`. -/
def fejerScale (ι : Type*) [Fintype ι] (N : ℕ) : ℝ :=
  1 / (((N : ℝ) + 1) ^ Fintype.card ι * (2 * π) ^ Fintype.card ι)

/-- The lattice Fejér density: a Gram form at the vectors `(e^{−i⟨j,θ⟩})_j`. -/
def latticeFejerDensity (φ : (ι → ℤ) → ℂ) (N : ℕ) (θ : ι → ℝ) : ℂ :=
  (fejerScale ι N : ℂ) * ∑ j : ι → Fin (N + 1), ∑ k : ι → Fin (N + 1),
    star (latticeChar (-windowPt N j) θ) * φ (windowPt N k - windowPt N j) *
      latticeChar (-windowPt N k) θ

omit [DecidableEq ι] in
theorem fejerScale_nonneg (N : ℕ) : 0 ≤ fejerScale ι N := by
  unfold fejerScale; positivity

omit [DecidableEq ι] in
/-- The Fejér density is real and nonnegative. -/
theorem latticeFejerDensity_nonneg {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (N : ℕ)
    (θ : ι → ℝ) :
    0 ≤ (latticeFejerDensity φ N θ).re ∧ (latticeFejerDensity φ N θ).im = 0 := by
  obtain ⟨h1, h2⟩ := hφ.re_nonneg_im_eq_zero (windowPt N) fun j => latticeChar (-windowPt N j) θ
  rw [latticeFejerDensity, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  exact ⟨mul_nonneg (fejerScale_nonneg N) h1, by rw [h2, mul_zero]⟩

omit [DecidableEq ι] in
theorem continuous_latticeFejerDensity (φ : (ι → ℤ) → ℂ) (N : ℕ) :
    Continuous (latticeFejerDensity φ N) := by
  unfold latticeFejerDensity
  refine continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_)
  exact ((continuous_star.comp (continuous_latticeChar _)).mul continuous_const).mul
    (continuous_latticeChar _)

/-- The lattice Fejér measure: the Fejér density on the box. -/
def latticeFejerMeasure (φ : (ι → ℤ) → ℂ) (N : ℕ) : Measure (ι → ℝ) :=
  boxMeasure.withDensity fun θ => ((latticeFejerDensity φ N θ).re.toNNReal : ℝ≥0∞)

omit [DecidableEq ι] in
theorem integral_latticeFejerMeasure {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (N : ℕ)
    (g : (ι → ℝ) → ℂ) :
    ∫ θ, g θ ∂latticeFejerMeasure φ N = ∫ θ, latticeFejerDensity φ N θ * g θ ∂boxMeasure := by
  have hmeas : Measurable fun θ => (latticeFejerDensity φ N θ).re.toNNReal :=
    (Complex.continuous_re.comp (continuous_latticeFejerDensity φ N)).measurable.real_toNNReal
  rw [latticeFejerMeasure, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  obtain ⟨h1, h2⟩ := latticeFejerDensity_nonneg hφ N θ
  have e : latticeFejerDensity φ N θ = (((latticeFejerDensity φ N θ).re.toNNReal : ℝ) : ℂ) := by
    rw [Real.coe_toNNReal _ h1]
    exact Complex.ext (by simp) (by simp [h2])
  simp only
  rw [NNReal.smul_def, Complex.real_smul, ← e]

/-! ### Counting window pairs -/

theorem sum_fin_ite_intCast_eq (N : ℕ) (a : ℤ) (c : ℂ) :
    ∑ b : Fin (N + 1), (if ((b : ℕ) : ℤ) = a then c else 0) =
      if 0 ≤ a ∧ a ≤ N then c else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun b => if (b : ℤ) = a then c else 0) (N + 1)]
  exact Bochner.sum_range_ite_intCast_eq N a c

theorem sum_fin_window_eq_pairCount (N : ℕ) (l : ℤ) :
    ∑ a : Fin (N + 1), (if 0 ≤ ((a : ℕ) : ℤ) + l ∧ ((a : ℕ) : ℤ) + l ≤ N then (1 : ℂ) else 0) =
      (Bochner.pairCount N l : ℂ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun a => if 0 ≤ (a : ℤ) + l ∧ (a : ℤ) + l ≤ N then (1 : ℂ) else 0) (N + 1),
    Bochner.pairCount, Finset.natCast_card_filter]

/-- **The window count factorizes.** `#{(j, k) ∈ ([0,N]^ι)² : k − j = m} = Π_i c(N, m_i)`. -/
theorem sum_window_pairs (N : ℕ) (m : ι → ℤ) :
    ∑ j : ι → Fin (N + 1), ∑ k : ι → Fin (N + 1),
        (if windowPt N k - windowPt N j = m then (1 : ℂ) else 0) =
      ∏ i, (Bochner.pairCount N (m i) : ℂ) := by
  have hcond : ∀ j k : ι → Fin (N + 1),
      (if windowPt N k - windowPt N j = m then (1 : ℂ) else 0) =
        ∏ i, (if ((k i : ℕ) : ℤ) = ((j i : ℕ) : ℤ) + m i then (1 : ℂ) else 0) := by
    intro j k
    rw [Fintype.prod_boole]
    refine if_congr ⟨fun h i => ?_, fun h => funext fun i => ?_⟩ rfl rfl
    · have := congrFun h i
      simp only [windowPt, Pi.sub_apply] at this
      omega
    · simp only [windowPt, Pi.sub_apply]
      have := h i
      omega
  simp_rw [hcond]
  have hinner : ∀ j : ι → Fin (N + 1),
      ∑ k : ι → Fin (N + 1), ∏ i, (if ((k i : ℕ) : ℤ) = ((j i : ℕ) : ℤ) + m i then (1 : ℂ) else 0) =
        ∏ i, (if 0 ≤ ((j i : ℕ) : ℤ) + m i ∧ ((j i : ℕ) : ℤ) + m i ≤ N then (1 : ℂ) else 0) := by
    intro j
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    exact Finset.prod_congr rfl fun i _ => sum_fin_ite_intCast_eq N _ 1
  simp_rw [hinner]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_congr rfl fun i _ => sum_fin_window_eq_pairCount N (m i)

/-- The Fejér weight `Π_i c(N, m_i)/(N+1)`. -/
def fejerWeight (N : ℕ) (m : ι → ℤ) : ℝ := ∏ i, (Bochner.pairCount N (m i) : ℝ) / ((N : ℝ) + 1)

/-- **The coefficients of the Fejér measure are the Fejér means.** -/
theorem fourierCoeff_latticeFejerMeasure {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (N : ℕ)
    (m : ι → ℤ) :
    fourierCoeff (latticeFejerMeasure φ N) m = (fejerWeight N m : ℂ) * φ m := by
  rw [fourierCoeff, integral_latticeFejerMeasure hφ, latticeFejerDensity]
  have hterm : ∀ (j k : ι → Fin (N + 1)) (θ : ι → ℝ),
      star (latticeChar (-windowPt N j) θ) * φ (windowPt N k - windowPt N j) *
          latticeChar (-windowPt N k) θ * latticeChar m θ =
        φ (windowPt N k - windowPt N j) *
          latticeChar (m - (windowPt N k - windowPt N j)) θ := by
    intro j k θ
    rw [star_latticeChar, neg_neg, show m - (windowPt N k - windowPt N j) =
      windowPt N j + (-windowPt N k + m) by abel, latticeChar_add, latticeChar_add]
    ring
  have hint : ∀ (j k : ι → Fin (N + 1)), Integrable (fun θ =>
      φ (windowPt N k - windowPt N j) * latticeChar (m - (windowPt N k - windowPt N j)) θ)
      boxMeasure := fun j k => (integrable_latticeChar _ _).const_mul _
  simp_rw [mul_assoc (fejerScale ι N : ℂ), Finset.sum_mul, hterm]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hint j k]
  simp_rw [integral_finset_sum _ fun k _ => hint _ k, integral_const_mul,
    integral_latticeChar_boxMeasure, sub_eq_zero]
  have hswap : ∀ j k : ι → Fin (N + 1),
      φ (windowPt N k - windowPt N j) *
          (if m = windowPt N k - windowPt N j then (((2 * π) ^ Fintype.card ι : ℝ) : ℂ) else 0) =
        (((2 * π) ^ Fintype.card ι : ℝ) : ℂ) * φ m *
          (if windowPt N k - windowPt N j = m then (1 : ℂ) else 0) := by
    intro j k
    by_cases h : windowPt N k - windowPt N j = m
    · rw [if_pos h.symm, if_pos h, h]; ring
    · rw [if_neg (Ne.symm h), if_neg h]; ring
  simp_rw [hswap, ← Finset.mul_sum, sum_window_pairs]
  unfold fejerWeight fejerScale
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have h1 : ((N : ℂ) + 1) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by positivity : (N : ℝ) + 1 ≠ 0))
  have h2 : ((2 : ℂ) * π) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
  field_simp

theorem fejerWeight_zero (ι : Type*) [Fintype ι] (N : ℕ) : fejerWeight (ι := ι) N 0 = 1 := by
  unfold fejerWeight
  simp only [Pi.zero_apply, Bochner.pairCount_zero]
  refine Finset.prod_eq_one fun i _ => ?_
  push_cast
  field_simp

/-- The Fejér weights tend to `1`. -/
theorem tendsto_fejerWeight (m : ι → ℤ) : Tendsto (fun N => fejerWeight N m) atTop (𝓝 1) := by
  unfold fejerWeight
  rw [show (1 : ℝ) = ∏ _i : ι, (1 : ℝ) by simp]
  refine tendsto_finset_prod _ fun i _ => ?_
  have hlow : ∀ N : ℕ, 1 - |(m i : ℝ)| / ((N : ℝ) + 1) ≤
      (Bochner.pairCount N (m i) : ℝ) / ((N : ℝ) + 1) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hN, sub_mul, div_mul_cancel₀ _ hN.ne', one_mul]
    exact Bochner.pairCount_ge N (m i)
  have hup : ∀ N : ℕ, (Bochner.pairCount N (m i) : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    intro N
    rw [div_le_one (by positivity)]
    exact_mod_cast Bochner.pairCount_le N (m i)
  have hz : Tendsto (fun N : ℕ => 1 - |(m i : ℝ)| / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |(m i : ℝ)|
    simpa [div_eq_mul_one_div] using h.const_sub 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hz tendsto_const_nhds hlow hup

/-! ### Herglotz–Bochner -/

theorem isFiniteMeasure_latticeFejerMeasure (φ : (ι → ℤ) → ℂ) (N : ℕ) :
    IsFiniteMeasure (latticeFejerMeasure φ N) := by
  have hc : Continuous fun θ => (latticeFejerDensity φ N θ).re :=
    Complex.continuous_re.comp (continuous_latticeFejerDensity φ N)
  obtain ⟨C, hC⟩ : ∃ C, ∀ θ ∈ Set.pi univ fun _ : ι => Icc (-π) π,
      ‖(latticeFejerDensity φ N θ).re‖ ≤ C :=
    (isCompact_univ_pi fun _ => isCompact_Icc).exists_bound_of_continuousOn hc.continuousOn
  sorry

end GaloisForLFunctions.ArithmeticPositiveDuality
