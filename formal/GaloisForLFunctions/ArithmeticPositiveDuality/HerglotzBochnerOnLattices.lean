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
open scoped ComplexConjugate BigOperators Real ENNReal NNReal BoundedContinuousFunction

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

omit [Fintype ι] [DecidableEq ι] in
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

omit [Fintype ι] [DecidableEq ι] in
theorem IsPosDefOnLattice.re_nonneg_im_eq_zero {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ)
    {κ : Type*} [Fintype κ] (x : κ → ι → ℤ) (c : κ → ℂ) :
    0 ≤ (∑ a, ∑ b, star (c a) * φ (x b - x a) * c b).re ∧
      (∑ a, ∑ b, star (c a) * φ (x b - x a) * c b).im = 0 := by
  obtain ⟨r, hr, h⟩ := hφ.form x c
  rw [h]
  simp [hr]

omit [Fintype ι] [DecidableEq ι] in
theorem IsPosDefOnLattice.zero {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) :
    0 ≤ (φ 0).re ∧ (φ 0).im = 0 := by
  have h := hφ.re_nonneg_im_eq_zero (κ := Unit) (fun _ => 0) (fun _ => 1)
  simpa using h

omit [Fintype ι] [DecidableEq ι] in
/-- The `2 × 2` form at `0, m`. -/
theorem IsPosDefOnLattice.two_form {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (m : ι → ℤ)
    (a b : ℂ) :
    0 ≤ (star a * φ 0 * a + star a * φ m * b + star b * φ (-m) * a + star b * φ 0 * b).re ∧
      (star a * φ 0 * a + star a * φ m * b + star b * φ (-m) * a + star b * φ 0 * b).im = 0 := by
  have h := hφ.re_nonneg_im_eq_zero (κ := Fin 2) ![0, m] ![a, b]
  simpa [Fin.sum_univ_two, add_assoc] using h

omit [Fintype ι] [DecidableEq ι] in
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

omit [Fintype ι] [DecidableEq ι] in
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

omit [Fintype ι] [DecidableEq ι] in
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
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((integrable_latticeChar μ _).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => ((integrable_latticeChar μ _).const_mul _).mul_const _]
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

/-- The Fejér density is real and nonnegative. -/
theorem latticeFejerDensity_nonneg {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (N : ℕ)
    (θ : ι → ℝ) :
    0 ≤ (latticeFejerDensity φ N θ).re ∧ (latticeFejerDensity φ N θ).im = 0 := by
  obtain ⟨h1, h2⟩ := hφ.re_nonneg_im_eq_zero (windowPt N) fun j => latticeChar (-windowPt N j) θ
  rw [latticeFejerDensity, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  exact ⟨mul_nonneg (fejerScale_nonneg N) h1, by rw [h2, mul_zero]⟩

theorem continuous_latticeFejerDensity (φ : (ι → ℤ) → ℂ) (N : ℕ) :
    Continuous (latticeFejerDensity φ N) := by
  unfold latticeFejerDensity
  refine continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_)
  exact ((continuous_star.comp (continuous_latticeChar _)).mul continuous_const).mul
    (continuous_latticeChar _)

/-- The lattice Fejér measure: the Fejér density on the box. -/
def latticeFejerMeasure (φ : (ι → ℤ) → ℂ) (N : ℕ) : Measure (ι → ℝ) :=
  boxMeasure.withDensity fun θ => ((latticeFejerDensity φ N θ).re.toNNReal : ℝ≥0∞)

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
    refine (Fintype.prod_sum (fun i (b : Fin (N + 1)) =>
      if ((b : ℕ) : ℤ) = ((j i : ℕ) : ℤ) + m i then (1 : ℂ) else 0)).symm.trans ?_
    exact Finset.prod_congr rfl fun i _ => sum_fin_ite_intCast_eq N _ 1
  simp_rw [hinner]
  refine (Fintype.prod_sum (fun i (a : Fin (N + 1)) =>
    if 0 ≤ ((a : ℕ) : ℤ) + m i ∧ ((a : ℕ) : ℤ) + m i ≤ N then (1 : ℂ) else 0)).symm.trans ?_
  exact Finset.prod_congr rfl fun i _ => sum_fin_window_eq_pairCount N (m i)

/-- The Fejér weight `Π_i c(N, m_i)/(N+1)`. -/
def fejerWeight (N : ℕ) (m : ι → ℤ) : ℝ := ∏ i, (Bochner.pairCount N (m i) : ℝ) / ((N : ℝ) + 1)

/-- **The coefficients of the Fejér measure are the Fejér means.** -/
theorem fourierCoeff_latticeFejerMeasure {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) (N : ℕ)
    (m : ι → ℤ) :
    fourierCoeff (latticeFejerMeasure φ N) m = (fejerWeight N m : ℂ) * φ m := by
  rw [fourierCoeff, integral_latticeFejerMeasure hφ]
  unfold latticeFejerDensity
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
  rw [integral_const_mul, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ k, integral_const_mul,
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

omit [DecidableEq ι] in
/-- The Fejér weights tend to `1`. -/
theorem tendsto_fejerWeight (m : ι → ℤ) : Tendsto (fun N => fejerWeight N m) atTop (𝓝 1) := by
  unfold fejerWeight
  suffices h : ∀ i ∈ (Finset.univ : Finset ι), Tendsto
      (fun N : ℕ => (Bochner.pairCount N (m i) : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 1) by
    have := tendsto_finsetProd Finset.univ h
    rwa [Finset.prod_const_one] at this
  intro i _
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
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |(m i : ℝ)|).const_sub 1
    rw [mul_zero, sub_zero] at h
    exact h.congr fun N => by rw [mul_one_div]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hz tendsto_const_nhds hlow hup

/-! ### Herglotz–Bochner -/

theorem isFiniteMeasure_latticeFejerMeasure (φ : (ι → ℤ) → ℂ) (N : ℕ) :
    IsFiniteMeasure (latticeFejerMeasure φ N) := by
  have hc : Continuous fun θ => (latticeFejerDensity φ N θ).re :=
    Complex.continuous_re.comp (continuous_latticeFejerDensity φ N)
  have hb : ∀ θ, ‖(latticeFejerDensity φ N θ).re‖ ≤ fejerScale ι N *
      ∑ j : ι → Fin (N + 1), ∑ k : ι → Fin (N + 1), ‖φ (windowPt N k - windowPt N j)‖ := by
    intro θ
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [latticeFejerDensity, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (fejerScale_nonneg N)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))) (fejerScale_nonneg N)
    rw [norm_mul, norm_mul, norm_star, norm_latticeChar, norm_latticeChar, one_mul, mul_one]
  have hint : Integrable (fun θ => (latticeFejerDensity φ N θ).re) boxMeasure :=
    Integrable.of_bound hc.aestronglyMeasurable _ (Eventually.of_forall hb)
  exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral

/-- The closed box `[−π, π]^ι`. -/
def closedBox : Set (ι → ℝ) := Set.pi univ fun _ => Icc (-π) π

omit [DecidableEq ι] in
theorem boxMeasure_compl_closedBox : boxMeasure (closedBoxᶜ : Set (ι → ℝ)) = 0 := by
  have hmeas : MeasurableSet (closedBox : Set (ι → ℝ)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  rw [measure_compl hmeas (measure_ne_top _ _), boxMeasure, closedBox, Measure.pi_pi,
    ← Set.pi_univ, Measure.pi_pi]
  simp only [Measure.restrict_apply measurableSet_Icc, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Set.inter_eq_right.mpr Ioc_subset_Icc_self, tsub_self]

theorem latticeFejerMeasure_compl_closedBox (φ : (ι → ℤ) → ℂ) (N : ℕ) :
    latticeFejerMeasure φ N (closedBoxᶜ : Set (ι → ℝ)) = 0 :=
  withDensity_absolutelyContinuous _ _ boxMeasure_compl_closedBox

theorem isProbabilityMeasure_latticeFejerMeasure {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ)
    (hφ0 : φ 0 = 1) (N : ℕ) : IsProbabilityMeasure (latticeFejerMeasure φ N) := by
  haveI := isFiniteMeasure_latticeFejerMeasure φ N
  constructor
  have h := fourierCoeff_latticeFejerMeasure hφ N 0
  rw [fejerWeight_zero, hφ0, fourierCoeff] at h
  simp only [latticeChar_zero, integral_const, Complex.real_smul, mul_one, Complex.ofReal_one]
    at h
  have hr : (latticeFejerMeasure φ N).real univ = 1 := by exact_mod_cast h
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ univ)]
  simp only [Measure.real] at hr
  rw [hr, ENNReal.ofReal_one]

/-- **Herglotz–Bochner, normalized.** A positive-definite `φ` on `ℤ^ι` with `φ(0) = 1` is the
coefficient sequence of a probability measure. -/
theorem exists_probabilityMeasure_fourierCoeff_eq {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ)
    (hφ0 : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure (ι → ℝ), ∀ m, fourierCoeff (μ : Measure (ι → ℝ)) m = φ m := by
  set seq : ℕ → ProbabilityMeasure (ι → ℝ) := fun N =>
    ⟨latticeFejerMeasure φ N, isProbabilityMeasure_latticeFejerMeasure hφ hφ0 N⟩
  have htight : IsTightMeasureSet {x | ∃ μ ∈ range seq, (μ : Measure (ι → ℝ)) = x} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε _
    refine ⟨closedBox, isCompact_univ_pi fun _ => isCompact_Icc, ?_⟩
    rintro _ ⟨μ, ⟨N, rfl⟩, rfl⟩
    rw [show ((seq N : ProbabilityMeasure (ι → ℝ)) : Measure (ι → ℝ)) =
      latticeFejerMeasure φ N from rfl, latticeFejerMeasure_compl_closedBox]
    exact zero_le
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨μ₀, -, σ, hσ, hlim⟩ := hcomp.tendsto_subseq (x := seq)
    (fun n => subset_closure (mem_range_self n))
  refine ⟨μ₀, fun m => ?_⟩
  have hconv := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    (latticeCharBCF m)
  have hseq : ∀ N, ∫ θ, latticeCharBCF m θ ∂(seq N : Measure (ι → ℝ)) =
      (fejerWeight N m : ℂ) * φ m := fun N => fourierCoeff_latticeFejerMeasure hφ N m
  have hlim2 : Tendsto (fun n => (fejerWeight (σ n) m : ℂ) * φ m) atTop (𝓝 (φ m)) := by
    have := ((Complex.continuous_ofReal.tendsto 1).comp
      ((tendsto_fejerWeight m).comp hσ.tendsto_atTop)).mul_const (φ m)
    simpa using this
  refine tendsto_nhds_unique ?_ hlim2
  have hconv' : Tendsto (fun n => ∫ θ, latticeCharBCF m θ ∂(seq (σ n) : Measure (ι → ℝ)))
      atTop (𝓝 (∫ θ, latticeCharBCF m θ ∂(μ₀ : Measure (ι → ℝ)))) := hconv
  simp only [hseq] at hconv'
  exact hconv'

/-- **Herglotz–Bochner on `ℤ^ι`.** A positive-definite function on `ℤ^ι` is the coefficient
sequence of a finite positive measure. -/
theorem exists_measure_fourierCoeff_eq {φ : (ι → ℤ) → ℂ} (hφ : IsPosDefOnLattice φ) :
    ∃ μ : Measure (ι → ℝ), IsFiniteMeasure μ ∧ ∀ m, fourierCoeff μ m = φ m := by
  obtain ⟨hp0, hpim⟩ := hφ.zero
  set p : ℝ := (φ 0).re with hp
  rcases eq_or_lt_of_le hp0 with hp00 | hppos
  · refine ⟨0, inferInstance, fun m => ?_⟩
    have := hφ.norm_le m
    rw [← hp, ← hp00] at this
    rw [norm_le_zero_iff.mp this, fourierCoeff, integral_zero_measure]
  · have hψ := hφ.const_mul (by positivity : (0 : ℝ) ≤ 1 / p)
    have hφ0 : φ 0 = (p : ℂ) := Complex.ext (by simp [hp]) (by simp [hpim])
    have hpc : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hppos.ne'
    have hψ0 : (fun m => ((1 / p : ℝ) : ℂ) * φ m) 0 = 1 := by
      simp only [hφ0]
      push_cast
      field_simp
    obtain ⟨μ₀, hμ₀⟩ := exists_probabilityMeasure_fourierCoeff_eq hψ hψ0
    refine ⟨ENNReal.ofReal p • (μ₀ : Measure (ι → ℝ)), ⟨?_⟩, fun m => ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
    rw [fourierCoeff, integral_smul_measure, ← fourierCoeff, hμ₀ m,
      ENNReal.toReal_ofReal hppos.le, Complex.real_smul]
    push_cast
    field_simp

/-- **Herglotz–Bochner, both directions.** -/
theorem isPosDefOnLattice_iff (φ : (ι → ℤ) → ℂ) :
    IsPosDefOnLattice φ ↔
      ∃ μ : Measure (ι → ℝ), IsFiniteMeasure μ ∧ ∀ m, fourierCoeff μ m = φ m := by
  constructor
  · exact exists_measure_fourierCoeff_eq
  · rintro ⟨μ, hμ, hφ⟩
    rw [show φ = fourierCoeff μ from funext fun m => (hφ m).symm]
    exact isPosDefOnLattice_fourierCoeff μ

/-! ### Restriction to a finite-rank subgroup: the Kronecker push-forward -/

/-- The Kronecker line `t ↦ (γ_i t)_i`. -/
def kroneckerLine (γ : ι → ℝ) (t : ℝ) : ι → ℝ := fun i => γ i * t

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_kroneckerLine (γ : ι → ℝ) : Measurable (kroneckerLine γ) :=
  measurable_pi_lambda _ fun _ => measurable_const.mul measurable_id

omit [DecidableEq ι] in
/-- **Restriction is push-forward.** The characteristic function of `ν` on the subgroup
`{⟨m, γ⟩ : m ∈ ℤ^ι}` of `ℝ` is the coefficient sequence of the push-forward of `ν` along the
Kronecker line. -/
theorem fourierCoeff_map_kroneckerLine (ν : Measure ℝ) (γ : ι → ℝ) (m : ι → ℤ) :
    fourierCoeff (ν.map (kroneckerLine γ)) m = charFun ν (pairing m γ) := by
  rw [fourierCoeff, integral_map (measurable_kroneckerLine γ).aemeasurable
    (continuous_latticeChar m).aestronglyMeasurable, charFun_apply_real]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [latticeChar, pairing, kroneckerLine]
  have e : (∑ i, (m i : ℝ) * (γ i * t)) = (∑ i, (m i : ℝ) * γ i) * t := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  push_cast
  ring_nf

omit [DecidableEq ι] in
/-- The restriction of a characteristic function to `m ↦ ⟨m, γ⟩` is positive definite on `ℤ^ι`. -/
theorem isPosDefOnLattice_charFun_comp (ν : Measure ℝ) [IsFiniteMeasure ν] (γ : ι → ℝ) :
    IsPosDefOnLattice fun m => charFun ν (pairing m γ) := by
  have h : fourierCoeff (ν.map (kroneckerLine γ)) = fun m => charFun ν (pairing m γ) :=
    funext fun m => fourierCoeff_map_kroneckerLine ν γ m
  rw [← h]
  exact isPosDefOnLattice_fourierCoeff _

end GaloisForLFunctions.ArithmeticPositiveDuality

