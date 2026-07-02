/-
# The imaginary-axis tip `z₀ = i·√(β+c)` and real-pair tip separation (OP4 prep B)

The explicit tip candidate of open problem 04, formalized.  A purely imaginary point `it` maps in
one quadratic step to the real point `c − t²`, so the imaginary slice of the filled Julia set is
the segment `i·[−t_c, t_c]` with `t_c = √(β+c)` (`tipHeight`).  Its endpoint `imagTip c = i·t_c`
is a Julia (frontier) point.  On `(−2, 0]` the height `c ↦ β(c)+c = 1 − (√(1−4c)−1)²/4` is
strictly increasing, so for a distinct real pair `c₂ < c₁ ≤ 0` the tip of `K_{c₁}` lies outside
`K_{c₂}` with a `K_{c₂}`-free ball around it.  This is every clause of the OP4 tip **except** the
hole/W-approach clause — the remaining open-math content.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.RealSliceDynamics

open Set Metric Bornology Filter Topology

namespace Bottcher

/-- The imaginary-axis exit height `t_c = √(β+c)` of the filled Julia set. -/
noncomputable def tipHeight (c : ℝ) : ℝ := Real.sqrt (betaFixed c + c)

theorem tipHeight_nonneg (c : ℝ) : 0 ≤ tipHeight c := Real.sqrt_nonneg _

/-- The imaginary-axis tip `z₀ = i·t_c` of the filled Julia set. -/
noncomputable def imagTip (c : ℝ) : ℂ := (tipHeight c : ℂ) * Complex.I

/-- **The imaginary slice of the filled Julia set**: for real `c ∈ [−2, 1/4]`,
`it ∈ K_c ↔ |t| ≤ t_c` — one quadratic step lands on the real axis at `c − t²`. -/
theorem imag_mem_filledJulia_iff {c t : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4) :
    ((t : ℂ) * Complex.I) ∈ filledJulia (c : ℂ) ↔ |t| ≤ tipHeight c := by
  have hβ := betaFixed_sq' hc4
  have hβc := betaFixed_add_nonneg hc2 hc4
  have hcast : quadratic (c : ℂ) ((t : ℂ) * Complex.I) = ((c - t ^ 2 : ℝ) : ℂ) := by
    rw [quadratic_apply, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [mem_filledJulia_iff_quadratic_mem, hcast, real_mem_filledJulia_iff hc2 hc4]
  unfold tipHeight
  constructor
  · intro h
    obtain ⟨hlo, _⟩ := abs_le.mp h
    have ht2 : t ^ 2 ≤ betaFixed c + c := by linarith
    have hs := Real.sqrt_le_sqrt ht2
    rwa [Real.sqrt_sq_eq_abs] at hs
  · intro h
    have ht2 : t ^ 2 ≤ betaFixed c + c := by
      have h2 := pow_le_pow_left₀ (abs_nonneg t) h 2
      rwa [sq_abs, Real.sq_sqrt hβc] at h2
    rw [abs_le]
    refine ⟨by linarith, ?_⟩
    linarith [sq_nonneg (betaFixed c), sq_nonneg t]

/-- The tip lies in the filled Julia set. -/
theorem imagTip_mem_filledJulia {c : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4) :
    imagTip c ∈ filledJulia (c : ℂ) := by
  rw [imagTip, imag_mem_filledJulia_iff hc2 hc4,
    abs_of_nonneg (tipHeight_nonneg c)]

/-- **The tip is a Julia point**: `imagTip c ∈ ∂K_c` — imaginary points just above it escape. -/
theorem imagTip_mem_frontier {c : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4) :
    imagTip c ∈ frontier (filledJulia (c : ℂ)) := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (imagTip_mem_filledJulia hc2 hc4), ?_⟩
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun n => ((tipHeight c + 1 / (n + 1) : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · intro n hmem
    rw [imag_mem_filledJulia_iff hc2 hc4] at hmem
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [abs_of_nonneg (by linarith [tipHeight_nonneg c])] at hmem
    linarith
  · have h5 : Tendsto (fun n : ℕ => tipHeight c + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (tipHeight c)) := by
      have h6 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (tipHeight c)
      simpa using h6
    have h7 : Continuous fun x : ℝ => ((x : ℂ) * Complex.I) := by fun_prop
    have h8 := (h7.tendsto _).comp h5
    simpa [imagTip, Function.comp_def] using h8

/-- **Tip-height monotonicity on `(−2, 0]`**: `β(c)+c = 1 − (√(1−4c)−1)²/4` is strictly
increasing for `c ≤ 0` (where `√(1−4c) ≥ 1`).  This FAILS on `(0, 1/4]` — the height peaks at
`c = 0` — which is why the tip-separation class is `(−2, 0]`. -/
theorem betaFixed_add_lt {c₁ c₂ : ℝ} (_h1 : -2 ≤ c₁) (hlt : c₁ < c₂) (h4 : c₂ ≤ 0) :
    betaFixed c₁ + c₁ < betaFixed c₂ + c₂ := by
  have hs₁ : Real.sqrt (1 - 4 * c₁) ^ 2 = 1 - 4 * c₁ := Real.sq_sqrt (by linarith)
  have hs₂ : Real.sqrt (1 - 4 * c₂) ^ 2 = 1 - 4 * c₂ := Real.sq_sqrt (by linarith)
  have hgt : Real.sqrt (1 - 4 * c₂) < Real.sqrt (1 - 4 * c₁) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hone : 1 ≤ Real.sqrt (1 - 4 * c₂) := by
    have h5 := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 - 4 * c₂ by linarith)
    rwa [Real.sqrt_one] at h5
  unfold betaFixed
  nlinarith [mul_self_lt_mul_self (by linarith : (0 : ℝ) ≤ Real.sqrt (1 - 4 * c₂) - 1)
    (by linarith : Real.sqrt (1 - 4 * c₂) - 1 < Real.sqrt (1 - 4 * c₁) - 1)]

theorem tipHeight_lt {c₁ c₂ : ℝ} (h1 : -2 ≤ c₁) (hlt : c₁ < c₂) (h4 : c₂ ≤ 0) :
    tipHeight c₁ < tipHeight c₂ := by
  unfold tipHeight
  exact Real.sqrt_lt_sqrt (betaFixed_add_nonneg h1 (by linarith))
    (betaFixed_add_lt h1 hlt h4)

/-- **Tip escape**: for a real pair `c₂ < c₁ ≤ 0` (both `> −2` not needed here), the tip of
`K_{c₁}` lies outside `K_{c₂}`. -/
theorem imagTip_notMem_filledJulia_of_lt {c₁ c₂ : ℝ} (h2 : -2 ≤ c₂) (hlt : c₂ < c₁)
    (h1 : c₁ ≤ 0) : imagTip c₁ ∉ filledJulia (c₂ : ℂ) := by
  intro hmem
  rw [imagTip, imag_mem_filledJulia_iff h2 (by linarith),
    abs_of_nonneg (tipHeight_nonneg c₁)] at hmem
  exact absurd hmem (not_le.mpr (tipHeight_lt h2 hlt h1))

/-- **The real-pair tip package (OP4, all but the hole clause)**: for a distinct real pair
`−2 ≤ c₂ < c₁ ≤ 0`, the explicit point `imagTip c₁ = i·√(β₁+c₁)` is a Julia point of `K_{c₁}`
outside `K_{c₂}`, with a `K_{c₂}`-free ball around it.  The sole missing OP4 clause is that
nearby basin points reach `∞` inside `ℂ ∖ (K_{c₁} ∪ K_{c₂})` — the open-math content. -/
theorem exists_real_pair_tip {c₁ c₂ : ℝ} (h2 : -2 ≤ c₂) (hlt : c₂ < c₁) (h1 : c₁ ≤ 0) :
    ∃ r : ℝ, 0 < r ∧
      imagTip c₁ ∈ frontier (filledJulia (c₁ : ℂ)) ∧
      imagTip c₁ ∉ filledJulia (c₂ : ℂ) ∧
      Metric.ball (imagTip c₁) r ∩ filledJulia (c₂ : ℂ) = ∅ := by
  have hnot := imagTip_notMem_filledJulia_of_lt h2 hlt h1
  have hopen : IsOpen (filledJulia (c₂ : ℂ))ᶜ := (isClosed_filledJulia _).isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hnot
  refine ⟨r, hr, imagTip_mem_frontier (by linarith) (by linarith), hnot, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hz1, hz2⟩
  exact (hball hz1) hz2

end Bottcher
