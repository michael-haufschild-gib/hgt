import GaloisForLFunctions.HTGeometry.EllipticGammaConeOrder

/-!
# The elliptic gamma source as a convergent atom series

Off its zeros the logarithmic derivative of an exponential cone product is the sum of the
logarithmic derivatives of its factors,

`(log Φ)′(z) = ∑_{j,k ≥ 0} -2πi e(j a + k b + z) / (1 - e(j a + k b + z))`,

and the elliptic gamma source `δ log Γ` is the difference of two such series.  This is the object
the principal-part normal form is written in.

Convergence is the same geometric domination as for the product itself: once the factor is within
`1/2` of one, its logarithmic derivative is at most `4π` times the deviation.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology Set

noncomputable section

/-- The logarithmic derivative of one cone factor. -/
theorem logDeriv_coneFactor (a b : ℂ) (n : ℕ × ℕ) (z : ℂ) :
    logDeriv (coneFactor a b n) z
      = -(expChar ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z) * (2 * (Real.pi : ℂ) * Complex.I))
        / coneFactor a b n z := by
  rw [logDeriv_apply, (hasDerivAt_coneFactor a b n z).deriv]

/-- **The atom bound.**  Where the factor is within `1/2` of one, its logarithmic derivative is at
most `4π` times the deviation. -/
theorem norm_logDeriv_coneFactor_le {a b : ℂ} {n : ℕ × ℕ} {z : ℂ}
    (hsmall : ‖coneFactor a b n z - 1‖ ≤ 1 / 2) :
    ‖logDeriv (coneFactor a b n) z‖ ≤ 4 * Real.pi * ‖coneFactor a b n z - 1‖ := by
  have hdev : coneFactor a b n z - 1 = -expChar ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z) := by
    rw [coneFactor]; ring
  have hnormdev : ‖expChar ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z)‖ = ‖coneFactor a b n z - 1‖ := by
    rw [hdev, norm_neg]
  have hlow : (1 : ℝ) / 2 ≤ ‖coneFactor a b n z‖ := by
    have htri : ‖(1 : ℂ)‖ - ‖coneFactor a b n z - 1‖ ≤ ‖coneFactor a b n z‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - coneFactor a b n z)
      have hrw : (1 : ℂ) - (1 - coneFactor a b n z) = coneFactor a b n z := by ring
      rw [hrw] at this
      have hsym : ‖(1 : ℂ) - coneFactor a b n z‖ = ‖coneFactor a b n z - 1‖ := norm_sub_rev _ _
      rw [hsym] at this
      exact this
    rw [norm_one] at htri
    linarith
  have hpos : (0 : ℝ) < ‖coneFactor a b n z‖ := by linarith
  rw [logDeriv_coneFactor, norm_div, norm_neg, norm_mul, hnormdev]
  rw [div_le_iff₀ hpos]
  have hcst : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [hcst]
  have hdevnn : (0 : ℝ) ≤ ‖coneFactor a b n z - 1‖ := norm_nonneg _
  have hhalf : ‖coneFactor a b n z - 1‖ * (2 * Real.pi)
      = 4 * Real.pi * ‖coneFactor a b n z - 1‖ * (1 / 2) := by ring
  rw [hhalf]
  exact mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **Summability of the atom series.** -/
theorem summable_logDeriv_coneFactor {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    Summable fun n : ℕ × ℕ => logDeriv (coneFactor a b n) z := by
  have hdev : Summable fun n : ℕ × ℕ => ‖coneFactor a b n z - 1‖ :=
    summable_norm_coneFactor_sub_one ha hb z
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ × ℕ =>
    4 * Real.pi * ‖coneFactor a b n z - 1‖) (hdev.mul_left _) ?_
  have htend : ∀ᶠ n : ℕ × ℕ in cofinite, ‖coneFactor a b n z - 1‖ ≤ 1 / 2 := by
    have h0 := hdev.tendsto_cofinite_zero
    have h2 := h0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h2] with n hn
    exact le_of_lt hn
  filter_upwards [htend] with n hn
  exact norm_logDeriv_coneFactor_le hn

/-- **The cone source is the atom series.**  Off the zeros of the product, the logarithmic
derivative is the sum of the logarithmic derivatives of the factors. -/
theorem logDeriv_coneProduct_eq_tsum {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) {z : ℂ}
    (hz : ∀ n : ℕ × ℕ, coneFactor a b n z ≠ 0) :
    logDeriv (coneProduct a b) z = ∑' n : ℕ × ℕ, logDeriv (coneFactor a b n) z := by
  have hmult : MultipliableLocallyUniformlyOn (coneFactor a b) Set.univ :=
    ⟨_, hasProdLocallyUniformlyOn_coneFactor ha hb⟩
  have hprod : (∏' n : ℕ × ℕ, coneFactor a b n z) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (coneProduct_eq_zero_iff ha hb z).mp h
    exact hz n hn
  change logDeriv (fun x => ∏' n : ℕ × ℕ, coneFactor a b n x) z = _
  exact logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) hz
    (fun n => (differentiable_coneFactor a b n).differentiableOn)
    (summable_logDeriv_coneFactor ha hb z) hmult hprod

/-! ### The elliptic gamma source -/

/-- The elliptic gamma source `Ψ = δ log Γ`. -/
def ellipticGammaSource (a b : ℂ) : ℂ → ℂ := logDeriv (ellipticGammaCone a b)

/-- A period of a function is a period of its logarithmic derivative. -/
theorem logDeriv_of_periodic {f : ℂ → ℂ} {p : ℂ} (hper : ∀ w, f (w + p) = f w) (z : ℂ) :
    logDeriv f (z + p) = logDeriv f z := by
  have hfun : (fun w => f (w + p)) = f := funext hper
  have hd : deriv (fun w : ℂ => f (w + p)) z = deriv f (z + p) := deriv_comp_add_const f p z
  rw [hfun] at hd
  rw [logDeriv_apply, logDeriv_apply, ← hd, hper]

/-- **The source is `1`-periodic.** -/
theorem ellipticGammaSource_periodic (a b : ℂ) (z : ℂ) :
    ellipticGammaSource a b (z + 1) = ellipticGammaSource a b z :=
  logDeriv_of_periodic (ellipticGammaCone_periodic a b) z

/-- **The source splits into two cone sources.**  Off the zeros of both cone products,
`Ψ(z) = -(log Φ)′(a + b - z) - (log Φ)′(z)`. -/
theorem ellipticGammaSource_eq_sub {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) {z : ℂ}
    (hnum : coneProduct a b (a + b - z) ≠ 0) (hden : coneProduct a b z ≠ 0) :
    ellipticGammaSource a b z
      = -(logDeriv (coneProduct a b) (a + b - z)) - logDeriv (coneProduct a b) z := by
  have hnumdiff : DifferentiableAt ℂ (fun w => coneProduct a b (a + b - w)) z :=
    (differentiable_ellipticGammaConeNum ha hb) z
  have hdendiff : DifferentiableAt ℂ (coneProduct a b) z := (differentiable_coneProduct ha hb) z
  have hsplit : ellipticGammaSource a b z
      = logDeriv (fun w => coneProduct a b (a + b - w)) z - logDeriv (coneProduct a b) z := by
    rw [ellipticGammaSource, ellipticGammaCone]
    exact logDeriv_div z hnum hden hnumdiff hdendiff
  rw [hsplit]
  congr 1
  have hd : deriv (fun w => coneProduct a b (a + b - w)) z
      = -deriv (coneProduct a b) (a + b - z) := by
    have hinner : HasDerivAt (fun w : ℂ => a + b - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (a + b)
    have houter : HasDerivAt (coneProduct a b) (deriv (coneProduct a b) (a + b - z))
        (a + b - z) := ((differentiable_coneProduct ha hb) (a + b - z)).hasDerivAt
    have hcomp := houter.comp z hinner
    rw [Function.comp_def] at hcomp
    have hval : deriv (fun w => coneProduct a b (a + b - w)) z
        = deriv (coneProduct a b) (a + b - z) * -1 := hcomp.deriv
    rw [hval]
    ring
  rw [logDeriv_apply, logDeriv_apply, hd]
  field_simp

end

end GaloisForLFunctions.HTGeometry
