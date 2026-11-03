import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheFrozenFormGluesTwoWindows
import GaloisForLFunctions.RHTower.ChronologicalTailInjectivity

/-!
# The collar Hankel form

Across a cut the archimedean place and the pole couple a left test `f` to a right test `g` only
through the trivial-divisor moments (CSTW `momentPairing`):
`⟨μ(f), ν(g)⟩ = μ_{1/2}(f)ν_{1/2}(g) − Σ_k μ_{σ_k}(f)ν_{σ_k}(g)`, `μ_σ(f) = ∫f e^{−σu}`,
`ν_σ(g) = ∫g e^{σv}`, `σ_k = −(2(k+1) + ½)` the exponents of the trivial zeros. On
**reflection-paired** collar data `g = f∘R`, `R(v) = 2m − v`, the right moments are reflected left
moments, `ν_σ(f∘R) = e^{2mσ}μ_σ(f)` (`rightMoment_collarReflect`), and the coupling becomes the
**collar Hankel form** (`momentPairing_collarReflect`)

    𝓗_m(f) = e^m μ_{1/2}(f)² − Σ_k e^{2mσ_k} μ_{σ_k}(f)²:

one pole square against the squares of the trivial zeros. Its kernel is the collar kernel
`2cosh(x/2) − ω(x)` at `x = 2m − u − u'`, a Hankel kernel.

For collar tests supported in `[p, q]`, `q < m`:

* **The trivial-zero squares are summable with geometric decay**
  (`atom_trivial_le`, `summable_trivialSquares`): the `k`-th square is at most
  `e^{−(4k+5)(m − q)}‖f‖₁²`.
* **The trivial zeros see every collar test** (`eq_zero_of_trivialMoments_eq_zero`): if all
  `μ_{σ_k}(f)` vanish then `f = 0` (polynomial moments in `y = e^{2u}`).
* **Inertia** (`collarHankel_neg_of_poleMoment_zero`, `exists_collarHankel_nonpos`). `𝓗_m` is
  negative definite on the pole hyperplane `μ_{1/2}(f) = 0`; every plane of collar tests contains a
  nonzero test with `𝓗_m ≤ 0`. So the collar Hankel form has at most one positive square and
  infinitely many negative ones.
* **Finite-rank shadow** (`abs_collarHankel_sub_truncation_le`). Keeping the first `K` trivial
  zeros changes `𝓗_m(f)` by at most `‖f‖₁² e^{−(4K+5)(m−q)}/(1 − e^{−4(m−q)})`.

At a stage the left and right collars are reflection-paired by the window involution: on the
`σ_A`-even sector the frozen coupling is `+2𝓗`, negative definite on the pole hyperplane, and the
pieces' own forms must pay it; on the odd sector it is `−2𝓗`, a positive source there.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The reflection `v ↦ 2m − v` of a collar test. -/
def collarReflect (m : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun v => f (2 * m - v)

/-- The **collar Hankel form** `e^m μ_{1/2}(f)² − Σ_k e^{2mσ_k} μ_{σ_k}(f)²`. -/
def collarHankel (m : ℝ) (f : ℝ → ℝ) : ℝ :=
  Real.exp m * leftMoment f (1 / 2) ^ 2 -
    ∑' k : ℕ, Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2

/-- Right moments of a reflected test are reflected left moments. -/
theorem rightMoment_collarReflect (m σ : ℝ) (f : ℝ → ℝ) :
    rightMoment (collarReflect m f) σ = Real.exp (2 * m * σ) * leftMoment f σ := by
  unfold rightMoment leftMoment collarReflect
  set F : ℝ → ℝ := fun u => f u * Real.exp (σ * (2 * m - u))
  have h := integral_sub_left_eq_self (μ := volume) F (2 * m)
  calc (∫ v, f (2 * m - v) * Real.exp (σ * v)) = ∫ v, F (2 * m - v) :=
        integral_congr_ae (Eventually.of_forall fun v => by simp only [F, sub_sub_cancel])
    _ = ∫ v, F v := h
    _ = ∫ v, Real.exp (2 * m * σ) * (f v * Real.exp (-(σ * v))) :=
        integral_congr_ae (Eventually.of_forall fun v => by
          simp only [F]
          rw [show σ * (2 * m - v) = 2 * m * σ + -(σ * v) by ring, Real.exp_add]
          ring)
    _ = Real.exp (2 * m * σ) * ∫ v, f v * Real.exp (-(σ * v)) := integral_const_mul _ _

/-- **The coupling of reflection-paired collar data is the collar Hankel form.** -/
theorem momentPairing_collarReflect (m : ℝ) (f : ℝ → ℝ) :
    momentPairing f (collarReflect m f) = collarHankel m f := by
  unfold momentPairing collarHankel
  rw [rightMoment_collarReflect, show 2 * m * (1 / 2 : ℝ) = m by ring]
  congr 1
  · ring
  · exact tsum_congr fun k => by rw [rightMoment_collarReflect]; ring

/-- With the opposite sign of reflection the coupling is minus the collar Hankel form. -/
theorem momentPairing_neg_collarReflect (m : ℝ) (f : ℝ → ℝ) :
    momentPairing f (fun v => -collarReflect m f v) = -collarHankel m f := by
  have hneg : ∀ σ, rightMoment (fun v => -collarReflect m f v) σ =
      -rightMoment (collarReflect m f) σ := fun σ => by
    unfold rightMoment
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun v => by simp only; ring)
  rw [← momentPairing_collarReflect]
  unfold momentPairing
  simp_rw [hneg, mul_neg, tsum_neg]
  ring

variable {f : ℝ → ℝ} {p q m : ℝ}

theorem neg_trivialExponent_pos (k : ℕ) : 0 < -trivialExponent k := by
  unfold trivialExponent
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- **Size of a trivial moment.** For `f` vanishing beyond `q`, `|μ_{σ_k}(f)| ≤ e^{−σ_k q}‖f‖₁`. -/
theorem abs_leftMoment_trivial_le (hf : Continuous f) (hsupp : ∀ u, u ∉ Icc p q → f u = 0)
    (k : ℕ) :
    |leftMoment f (trivialExponent k)| ≤
      Real.exp (-(trivialExponent k * q)) * ∫ u, |f u| := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc hsupp
  have hσ := neg_trivialExponent_pos k
  unfold leftMoment
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono
    ((hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right).abs
    ((hf.abs.integrable_of_hasCompactSupport hfc.abs).const_mul _) fun u => ?_)
  simp only
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  by_cases hu : u ∈ Icc p q
  · have : Real.exp (-(trivialExponent k * u)) ≤ Real.exp (-(trivialExponent k * q)) :=
      Real.exp_le_exp.mpr (by nlinarith [hu.2])
    nlinarith [abs_nonneg (f u)]
  · simp [hsupp u hu]

/-- **Geometric decay of the trivial-zero squares.** -/
theorem atom_trivial_le (hf : Continuous f) (hsupp : ∀ u, u ∉ Icc p q → f u = 0) (k : ℕ) :
    Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2 ≤
      (∫ u, |f u|) ^ 2 * Real.exp (2 * trivialExponent k * (m - q)) := by
  have h := abs_leftMoment_trivial_le hf hsupp k
  have hsq : leftMoment f (trivialExponent k) ^ 2 ≤
      (Real.exp (-(trivialExponent k * q)) * ∫ u, |f u|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have he : Real.exp (2 * m * trivialExponent k) * Real.exp (-(trivialExponent k * q)) ^ 2 =
      Real.exp (2 * trivialExponent k * (m - q)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  calc Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2
      ≤ Real.exp (2 * m * trivialExponent k) *
          (Real.exp (-(trivialExponent k * q)) * ∫ u, |f u|) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = (∫ u, |f u|) ^ 2 * Real.exp (2 * trivialExponent k * (m - q)) := by
        rw [mul_pow, ← mul_assoc, he]; ring

/-- The geometric bound `e^{2σ_k(m−q)} = e^{−5(m−q)} (e^{−4(m−q)})^k`. -/
theorem exp_two_trivialExponent_mul (k : ℕ) (d : ℝ) :
    Real.exp (2 * trivialExponent k * d) = Real.exp (-(5 * d)) * Real.exp (-(4 * d)) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  unfold trivialExponent
  congr 1; ring

theorem summable_trivialSquares (hf : Continuous f) (hsupp : ∀ u, u ∉ Icc p q → f u = 0)
    (hqm : q < m) :
    Summable fun k : ℕ =>
      Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2 := by
  have hr : Real.exp (-(4 * (m - q))) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable fun k : ℕ => (∫ u, |f u|) ^ 2 * Real.exp (2 * trivialExponent k * (m - q)) := by
    simp_rw [exp_two_trivialExponent_mul]
    exact ((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
      (Real.exp (-(5 * (m - q))))).mul_left _
  exact hgeo.of_nonneg_of_le (fun k => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    (atom_trivial_le hf hsupp)

/-- **The trivial zeros see every collar test.** If every trivial moment of a continuous `f`
supported in `[p, q]` vanishes, then `f = 0`. -/
theorem eq_zero_of_trivialMoments_eq_zero (hf : Continuous f) (hsupp : ∀ u, u ∉ Icc p q → f u = 0)
    (hpq : p < q) (h0 : ∀ k : ℕ, leftMoment f (trivialExponent k) = 0) : ∀ u, f u = 0 := by
  set g : ℝ → ℝ := fun y => f (Real.log y / 2) * Real.exp (Real.log y / 4) / 2
  set E : ℝ → ℝ := fun u => Real.exp (2 * u)
  have hEd : ∀ u, HasDerivAt E (2 * Real.exp (2 * u)) u := fun u => by
    simpa [E, mul_comm] using ((hasDerivAt_id u).const_mul 2).exp
  have hEpos : ∀ u, 0 < E u := fun u => Real.exp_pos _
  have hgcont : ContinuousOn g (Ioi 0) := by
    have hlog : ContinuousOn Real.log (Ioi 0) :=
      Real.continuousOn_log.mono fun y hy => ne_of_gt hy
    exact ((hf.comp_continuousOn (hlog.div_const 2)).mul
      (Real.continuous_exp.comp_continuousOn (hlog.div_const 4))).div_const 2
  have hmom : ∀ n : ℕ, ∫ y in E p..E q, g y * y ^ n = 0 := by
    intro n
    have hcv := intervalIntegral.integral_comp_mul_deriv' (a := p) (b := q) (f := E)
      (f' := fun u => 2 * Real.exp (2 * u)) (g := fun y => g y * y ^ n)
      (fun u _ => hEd u) (by fun_prop)
      ((hgcont.mul (continuous_pow n).continuousOn).mono fun y ⟨u, _, hu⟩ => by
        rw [← hu]; exact hEpos u)
    rw [← hcv]
    have hpt : ∀ u, ((fun y => g y * y ^ n) ∘ E) u * (2 * Real.exp (2 * u)) =
        f u * Real.exp (-(trivialExponent n * u)) := fun u => by
      simp only [Function.comp, g, E, Real.log_exp]
      rw [show 2 * u / 2 = u by ring, show 2 * u / 4 = u / 2 by ring, ← Real.exp_nat_mul]
      have e : Real.exp (u / 2) / 2 * Real.exp (↑n * (2 * u)) * (2 * Real.exp (2 * u)) =
          Real.exp (-(trivialExponent n * u)) := by
        rw [show Real.exp (u / 2) / 2 * Real.exp (↑n * (2 * u)) * (2 * Real.exp (2 * u)) =
          Real.exp (u / 2 + ↑n * (2 * u) + 2 * u) by rw [Real.exp_add, Real.exp_add]; ring]
        unfold trivialExponent
        congr 1; ring
      rw [← e]; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_of_le hpq.le, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hsupp u hu]]
    exact h0 n
  have hEpq : E p < E q := Real.exp_lt_exp.mpr (by linarith)
  have hz := RHTower.eqOn_zero_of_moments_eq_zero hEpq
    (hgcont.mono fun y hy => lt_of_lt_of_le (hEpos p) hy.1) hmom
  intro u
  by_cases hu : u ∈ Icc p q
  · have hy : E u ∈ Icc (E p) (E q) :=
      ⟨Real.exp_le_exp.mpr (by linarith [hu.1]), Real.exp_le_exp.mpr (by linarith [hu.2])⟩
    have := hz hy
    simp only [g, E, Pi.zero_apply, Real.log_exp] at this
    rw [show 2 * u / 2 = u by ring] at this
    have hex : Real.exp (2 * u / 4) ≠ 0 := (Real.exp_pos _).ne'
    have : f u * Real.exp (2 * u / 4) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hex
  · exact hsupp u hu

/-- **The collar Hankel form is negative definite on the pole hyperplane.** -/
theorem collarHankel_neg_of_poleMoment_zero (hf : Continuous f)
    (hsupp : ∀ u, u ∉ Icc p q → f u = 0) (hpq : p < q) (hqm : q < m)
    (hpole : leftMoment f (1 / 2) = 0) (hne : ∃ u, f u ≠ 0) : collarHankel m f < 0 := by
  have hsum := summable_trivialSquares hf hsupp hqm
  have hnn : ∀ k : ℕ, 0 ≤ Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2 :=
    fun k => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, leftMoment f (trivialExponent k) ≠ 0 := by
    by_contra hall
    have hall' : ∀ k : ℕ, leftMoment f (trivialExponent k) = 0 := fun k => by
      by_contra hk; exact hall ⟨k, hk⟩
    obtain ⟨u, hu⟩ := hne
    exact hu (eq_zero_of_trivialMoments_eq_zero hf hsupp hpq hall' u)
  have hpos : 0 < ∑' k : ℕ, Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2 :=
    hsum.tsum_pos hnn k (mul_pos (Real.exp_pos _)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk))))
  unfold collarHankel
  rw [hpole]
  linarith

theorem leftMoment_add_smul {f₁ f₂ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hc₁ : HasCompactSupport f₁) (hc₂ : HasCompactSupport f₂) (α β σ : ℝ) :
    leftMoment (fun u => α * f₁ u + β * f₂ u) σ = α * leftMoment f₁ σ + β * leftMoment f₂ σ := by
  unfold leftMoment
  have i₁ : Integrable fun u => α * (f₁ u * Real.exp (-(σ * u))) :=
    ((h₁.mul (by fun_prop)).integrable_of_hasCompactSupport hc₁.mul_right).const_mul α
  have i₂ : Integrable fun u => β * (f₂ u * Real.exp (-(σ * u))) :=
    ((h₂.mul (by fun_prop)).integrable_of_hasCompactSupport hc₂.mul_right).const_mul β
  have hadd : (∫ u, (α * (f₁ u * Real.exp (-(σ * u))) + β * (f₂ u * Real.exp (-(σ * u))))) =
      (∫ u, α * (f₁ u * Real.exp (-(σ * u)))) + ∫ u, β * (f₂ u * Real.exp (-(σ * u))) :=
    integral_add i₁ i₂
  rw [integral_const_mul, integral_const_mul] at hadd
  rw [← hadd]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

/-- **At most one positive square.** Every plane of collar tests contains a nonzero combination
`αf₁ + βf₂`, `(α, β) ≠ 0`, with `𝓗_m ≤ 0`. -/
theorem exists_collarHankel_nonpos {f₁ f₂ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hc₁ : HasCompactSupport f₁) (hc₂ : HasCompactSupport f₂) (m : ℝ) :
    ∃ α β : ℝ, (α, β) ≠ (0, 0) ∧ collarHankel m (fun u => α * f₁ u + β * f₂ u) ≤ 0 := by
  have hT : ∀ g : ℝ → ℝ, leftMoment g (1 / 2) = 0 → collarHankel m g ≤ 0 := by
    intro g hg
    unfold collarHankel
    rw [hg]
    have : 0 ≤ ∑' k : ℕ, Real.exp (2 * m * trivialExponent k) * leftMoment g (trivialExponent k) ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    linarith
  by_cases h : leftMoment f₁ (1 / 2) = 0 ∧ leftMoment f₂ (1 / 2) = 0
  · refine ⟨1, 0, by simp, hT _ ?_⟩
    rw [leftMoment_add_smul h₁ h₂ hc₁ hc₂, h.1, h.2]; ring
  · refine ⟨leftMoment f₂ (1 / 2), -leftMoment f₁ (1 / 2), ?_, hT _ ?_⟩
    · intro he
      simp only [Prod.mk.injEq, neg_eq_zero] at he
      exact h ⟨he.2, he.1⟩
    · rw [leftMoment_add_smul h₁ h₂ hc₁ hc₂]; ring

/-- **Finite-rank shadow.** Keeping the first `K` trivial zeros changes the collar Hankel form by
at most `‖f‖₁² e^{−(4K+5)(m−q)}/(1 − e^{−4(m−q)})`. -/
theorem abs_collarHankel_sub_truncation_le (hf : Continuous f)
    (hsupp : ∀ u, u ∉ Icc p q → f u = 0) (hqm : q < m) (K : ℕ) :
    |collarHankel m f - (Real.exp m * leftMoment f (1 / 2) ^ 2 -
        ∑ k ∈ Finset.range K, Real.exp (2 * m * trivialExponent k) *
          leftMoment f (trivialExponent k) ^ 2)| ≤
      (∫ u, |f u|) ^ 2 * Real.exp (-(5 * (m - q))) * Real.exp (-(4 * (m - q))) ^ K /
        (1 - Real.exp (-(4 * (m - q)))) := by
  set a : ℕ → ℝ := fun k =>
    Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2
  have hsum : Summable a := summable_trivialSquares hf hsupp hqm
  have ha0 : ∀ k, 0 ≤ a k := fun k => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  set r := Real.exp (-(4 * (m - q)))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set C := (∫ u, |f u|) ^ 2 * Real.exp (-(5 * (m - q)))
  have hC0 : 0 ≤ C := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hbound : ∀ k, a k ≤ C * r ^ k := fun k => by
    have := atom_trivial_le (m := m) hf hsupp k
    rw [exp_two_trivialExponent_mul] at this
    simp only [a, C, r]
    linarith
  have htail : ∑' k : ℕ, a (k + K) ≤ C * r ^ K / (1 - r) := by
    have hg : Summable fun k : ℕ => C * r ^ K * r ^ k :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    calc ∑' k : ℕ, a (k + K) ≤ ∑' k : ℕ, C * r ^ K * r ^ k :=
          Summable.tsum_le_tsum (fun k => by rw [mul_assoc, ← pow_add, add_comm]; exact hbound _)
            ((summable_nat_add_iff K).mpr hsum) hg
      _ = C * r ^ K / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; ring
  have hsplit := hsum.sum_add_tsum_nat_add K
  have htail0 : 0 ≤ ∑' k : ℕ, a (k + K) := tsum_nonneg fun k => ha0 _
  unfold collarHankel
  rw [← hsplit]
  rw [show Real.exp m * leftMoment f (1 / 2) ^ 2 -
      ((∑ k ∈ Finset.range K, a k) + ∑' k : ℕ, a (k + K)) -
      (Real.exp m * leftMoment f (1 / 2) ^ 2 - ∑ k ∈ Finset.range K, a k) =
      -(∑' k : ℕ, a (k + K)) by ring, abs_neg, abs_of_nonneg htail0]
  exact htail

end GaloisForLFunctions.SignedWindowCriticality

end
