import GaloisForLFunctions.ArithmeticDiscreteness.ANearCoincidenceFlattensZeta

/-!
# Consistent tangencies are the only source of near-coincidences

A finite-prime carrier is an entire function `D(s) = G(p₁^{−s}, …, p_d^{−s})` whose derivative is
`D'(s) = H(p₁^{−s}, …, p_d^{−s})`, with `G, H` continuous (for a Dirichlet polynomial
`G(x) = Σ c_n x^n`, `H(x) = −Σ c_n (n · log p) x^n`). Its **Bohr lift** replaces `(p_i^{−s})` by an
arbitrary point `x` of the compact set

`K[a, b] = {x : ∃ σ ∈ [a, b], ∀ i, |x_i| = p_i^{−σ}}`,

the closure of the vertical translates of the strip `a ≤ Re s ≤ b`. A **consistent tangency** is a
point `x ∈ K[a, b]` with `G(x) = H(x) = 0`.

* **Tangency gap** (`exists_tangency_gap`). Without consistent tangencies, `|D'|` is bounded below
  by a positive constant at every zero in the strip: `|H|` attains a positive minimum on the
  compact set `K[a, b] ∩ {G = 0}`.
* **Uniform repulsion** (`uniform_repulsion_of_no_consistent_tangency`). If all zeros lie in
  `a ≤ Re s ≤ b` and there is no consistent tangency, distinct zeros are uniformly separated:
  two zeros at distance `h ≤ 1/4` force `|D'| ≤ 8Mh` (`norm_deriv_mul_le_of_two_zeros`), `M` the
  maximum of `|G|` on `K[a − 1, b + 1]`.

So near-coincidences at every scale require a consistent tangency of the Bohr lift. The Euler
product `∏(1 − p_i^{−s})` has one at `x = (1, …, 1)`, `σ = 0`, and indeed none of its repulsion is
uniform (`twoPrime_no_uniform_repulsion`); the trinomial `1 + 2^{−s} + 3^{−s}` has none
(`trinomial_uniform_repulsion`).
-/

open Complex Metric Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The coordinates `(p_i^{−s})_i` of a point of the Bohr lift. -/
def bohrPoint {d : ℕ} (p : Fin d → ℝ) (s : ℂ) : Fin d → ℂ := fun i => ((p i : ℝ) : ℂ) ^ (-s)

/-- The compact set `K[a, b]`, as the image of `[a, b] × (unit circle)^d`. -/
def bohrBand {d : ℕ} (p : Fin d → ℝ) (a b : ℝ) : Set (Fin d → ℂ) :=
  (fun z : ℝ × (Fin d → ℂ) => fun i => (((p i) ^ (-z.1) : ℝ) : ℂ) * z.2 i) ''
    (Icc a b ×ˢ Set.pi univ fun _ => sphere (0 : ℂ) 1)

theorem isCompact_bohrBand {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 < p i) (a b : ℝ) :
    IsCompact (bohrBand p a b) := by
  refine (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_sphere 0 1)).image ?_
  refine continuous_pi fun i => ?_
  refine Continuous.mul ?_ ((continuous_apply i).comp continuous_snd)
  exact Complex.continuous_ofReal.comp
    (continuous_const.rpow continuous_fst.neg fun _ => Or.inl (hp i).ne')

theorem bohrPoint_mem_bohrBand {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 < p i) {a b : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) : bohrPoint p s ∈ bohrBand p a b := by
  have hnorm : ∀ i, ‖bohrPoint p s i‖ = (p i) ^ (-s.re) := fun i => by
    rw [bohrPoint, Complex.norm_cpow_eq_rpow_re_of_pos (hp i), neg_re]
  have hpos : ∀ i, 0 < (p i) ^ (-s.re) := fun i => Real.rpow_pos_of_pos (hp i) _
  refine ⟨(s.re, fun i => bohrPoint p s i / (((p i) ^ (-s.re) : ℝ) : ℂ)), ⟨⟨ha, hb⟩, ?_⟩, ?_⟩
  · intro i _
    rw [mem_sphere_zero_iff_norm, norm_div, hnorm, norm_real, Real.norm_eq_abs,
      abs_of_pos (hpos i), div_self (hpos i).ne']
  · funext i
    have : (((p i) ^ (-s.re) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
    show (((p i) ^ (-s.re) : ℝ) : ℂ) * (bohrPoint p s i / (((p i) ^ (-s.re) : ℝ) : ℂ)) =
      bohrPoint p s i
    rw [mul_comm, div_mul_cancel₀ _ this]

/-- **Tangency gap.** If `G, H` are continuous and no point of `K[a, b]` has `G = H = 0`, there is
`η > 0` with `η ≤ |H(x)|` for every `x ∈ K[a, b]` with `G(x) = 0`. -/
theorem exists_tangency_gap {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 < p i) (a b : ℝ)
    {G H : (Fin d → ℂ) → ℂ} (hG : Continuous G) (hH : Continuous H)
    (hno : ∀ x ∈ bohrBand p a b, G x = 0 → H x ≠ 0) :
    ∃ η > 0, ∀ x ∈ bohrBand p a b, G x = 0 → η ≤ ‖H x‖ := by
  set Z := bohrBand p a b ∩ {x | G x = 0} with hZ
  have hZc : IsCompact Z := (isCompact_bohrBand p hp a b).inter_right (isClosed_eq hG continuous_const)
  rcases Z.eq_empty_or_nonempty with h0 | hne
  · exact ⟨1, one_pos, fun x hx hGx => absurd (show x ∈ Z from ⟨hx, hGx⟩) (by rw [h0]; exact id)⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hZc.exists_isMinOn hne (continuous_norm.comp hH).continuousOn
    refine ⟨‖H x₀‖, norm_pos_iff.mpr (hno x₀ hx₀.1 hx₀.2), fun x hx hGx => ?_⟩
    exact hmin ⟨hx, hGx⟩

/-- **Uniform repulsion without consistent tangencies.** Let `D` be entire with
`D(s) = G((p_i^{−s}))` and `D'(s) = H((p_i^{−s}))`, `G, H` continuous, all zeros in `a ≤ Re s ≤ b`,
and no point of `K[a, b]` with `G = H = 0`. Then distinct zeros are uniformly separated. -/
theorem uniform_repulsion_of_no_consistent_tangency {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 < p i)
    {a b : ℝ} {D : ℂ → ℂ} (hD : Differentiable ℂ D) {G H : (Fin d → ℂ) → ℂ}
    (hG : Continuous G) (hH : Continuous H) (hDG : ∀ s, D s = G (bohrPoint p s))
    (hDH : ∀ s, deriv D s = H (bohrPoint p s)) (hstrip : ∀ s, D s = 0 → a ≤ s.re ∧ s.re ≤ b)
    (hno : ∀ x ∈ bohrBand p a b, G x = 0 → H x ≠ 0) :
    ∃ δ > 0, ∀ s s' : ℂ, D s = 0 → D s' = 0 → s ≠ s' → δ ≤ ‖s' - s‖ := by
  obtain ⟨η, hη, hgap⟩ := exists_tangency_gap p hp a b hG hH hno
  -- `|G| ≤ M` on `K[a − 1, b + 1]`
  obtain ⟨M₀, hM₀⟩ := (isCompact_bohrBand p hp (a - 1) (b + 1)).exists_bound_of_continuousOn
    hG.continuousOn
  set M := max M₀ 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  refine ⟨min (1 / 4) (η / (8 * M)), lt_min (by norm_num) (by positivity),
    fun s s' hs hs' hne => ?_⟩
  by_cases hfar : 1 / 4 < ‖s' - s‖
  · exact (min_le_left _ _).trans hfar.le
  push Not at hfar
  obtain ⟨ha, hb⟩ := hstrip s hs
  have hbound : ∀ z ∈ closedBall s 1, ‖D z‖ ≤ M := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre := (abs_re_le_norm (z - s)).trans hz
    rw [sub_re] at hre
    rw [hDG]
    exact (hM₀ _ (bohrPoint_mem_bohrBand p hp (by linarith [(abs_le.mp hre).1])
      (by linarith [(abs_le.mp hre).2]))).trans (le_max_left _ _)
  have h := norm_deriv_mul_le_of_two_zeros isOpen_univ hD.differentiableOn (by norm_num : (0 : ℝ) < 1)
    (subset_univ _) hbound (by linarith : ‖s' - s‖ ≤ 1 / 4) hs hs'
  have hder : η ≤ ‖deriv D s‖ := by
    rw [hDH]
    exact hgap _ (bohrPoint_mem_bohrBand p hp ha hb) (by rw [← hDG]; exact hs)
  have hpos : 0 < ‖s' - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have h2 : η * ‖s' - s‖ ≤ 8 * M * ‖s' - s‖ ^ 2 := by
    have := (mul_le_mul_of_nonneg_right hder hpos.le).trans h
    linarith
  have h3 : η ≤ 8 * M * ‖s' - s‖ := by
    rw [sq, ← mul_assoc] at h2
    exact le_of_mul_le_mul_right h2 hpos
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
