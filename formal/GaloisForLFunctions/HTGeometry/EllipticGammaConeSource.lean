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

/-! ### The shift laws for the two sources -/

theorem logDeriv_comp_add_const (f : ℂ → ℂ) (c w : ℂ) :
    logDeriv (fun x => f (x + c)) w = logDeriv f (w + c) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]

/-- **The single-index source drops one atom under a `b`-shift.** -/
theorem logDeriv_singleProduct_shift {b : ℂ} (hb : 0 < b.im) {w : ℂ}
    (h0 : (1 : ℂ) - expChar w ≠ 0) (hP : singleProduct b (w + b) ≠ 0) :
    logDeriv (singleProduct b) w
      = logDeriv (fun x => 1 - expChar x) w + logDeriv (singleProduct b) (w + b) := by
  have hfun : singleProduct b = fun x => (1 - expChar x) * singleProduct b (x + b) := by
    funext x
    exact singleProduct_shift hb x
  have hd1 : DifferentiableAt ℂ (fun x : ℂ => 1 - expChar x) w := by
    unfold expChar
    fun_prop
  have hd2 : DifferentiableAt ℂ (fun x : ℂ => singleProduct b (x + b)) w := by
    have hcomp : Differentiable ℂ (fun x : ℂ => singleProduct b (x + b)) :=
      (differentiable_singleProduct hb).comp (by fun_prop)
    exact hcomp w
  conv_lhs => rw [hfun]
  rw [logDeriv_mul w h0 hP hd1 hd2, logDeriv_comp_add_const]

/-- **The cone source drops one single-index source under an `a`-shift.** -/
theorem logDeriv_coneProduct_shift {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) {w : ℂ}
    (hP : singleProduct b w ≠ 0) (hC : coneProduct a b (w + a) ≠ 0) :
    logDeriv (coneProduct a b) w
      = logDeriv (singleProduct b) w + logDeriv (coneProduct a b) (w + a) := by
  have hfun : coneProduct a b = fun x => singleProduct b x * coneProduct a b (x + a) := by
    funext x
    exact coneProduct_shift ha hb x
  have hd1 : DifferentiableAt ℂ (singleProduct b) w := (differentiable_singleProduct hb) w
  have hd2 : DifferentiableAt ℂ (fun x : ℂ => coneProduct a b (x + a)) w := by
    have hcomp : Differentiable ℂ (fun x : ℂ => coneProduct a b (x + a)) :=
      (differentiable_coneProduct ha hb).comp (by fun_prop)
    exact hcomp w
  conv_lhs => rw [hfun]
  rw [logDeriv_mul w hP hC hd1 hd2, logDeriv_comp_add_const]

/-! ### The atom identity behind the mixed constant -/

/-- The logarithmic derivative of the elementary atom. -/
theorem logDeriv_one_sub_expChar {w : ℂ} (_h : (1 : ℂ) - expChar w ≠ 0) :
    logDeriv (fun x => 1 - expChar x) w
      = -(expChar w * (2 * (Real.pi : ℂ) * Complex.I)) / (1 - expChar w) := by
  have hd : HasDerivAt (fun x : ℂ => 1 - expChar x)
      (-(expChar w * (2 * (Real.pi : ℂ) * Complex.I))) w := by
    have h1 : HasDerivAt (fun x : ℂ => 2 * (Real.pi : ℂ) * Complex.I * x)
        (2 * (Real.pi : ℂ) * Complex.I) w := by
      simpa using (hasDerivAt_id w).const_mul (2 * (Real.pi : ℂ) * Complex.I)
    exact h1.cexp.const_sub 1
  rw [logDeriv_apply, hd.deriv]

/-- **The two atoms cancel to one.**  For `e(z) ≠ 1`,
`e(z)/(1 - e(z)) + e(-z)/(1 - e(-z)) = -1`. -/
theorem expChar_atom_sum {z : ℂ} (h : (1 : ℂ) - expChar z ≠ 0)
    (_h' : (1 : ℂ) - expChar (-z) ≠ 0) :
    expChar z / (1 - expChar z) + expChar (-z) / (1 - expChar (-z)) = -1 := by
  have hmul : expChar (-z) * expChar z = 1 := expChar_neg_mul_self z
  have hz0 : expChar z ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact one_ne_zero hmul.symm
  have hinv : expChar (-z) = (expChar z)⁻¹ := by
    field_simp
    linear_combination hmul
  have hu1 : expChar z - 1 ≠ 0 := by
    intro hzz
    exact h (by linear_combination -hzz)
  rw [hinv]
  have hden : (1 : ℂ) - (expChar z)⁻¹ = (expChar z - 1) / expChar z := by
    field_simp
  rw [hden]
  field_simp
  ring

/-! ### The mixed difference of the source -/

/-- **The mixed difference of the elliptic gamma source is the constant `-2πi`.**  This is the
membership `Ψ ∈ Q`: `Ψ` is `1`-periodic and its mixed difference is a constant.

The eight cone-source terms pair off under the `a`-shift law into four single-index terms, those
pair off under the `b`-shift law into two atoms, and the two atoms cancel to `-1`. -/
theorem ellipticGammaSource_mixed_difference {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) {z : ℂ}
    (hez : (1 : ℂ) - expChar z ≠ 0) (hez' : (1 : ℂ) - expChar (-z) ≠ 0)
    (hC1 : coneProduct a b (-z) ≠ 0) (hC2 : coneProduct a b (z + a + b) ≠ 0)
    (hC3 : coneProduct a b (a + b - z) ≠ 0) (hC4 : coneProduct a b z ≠ 0)
    (hC5 : coneProduct a b (b - z) ≠ 0) (hC6 : coneProduct a b (z + a) ≠ 0)
    (hC7 : coneProduct a b (a - z) ≠ 0) (hC8 : coneProduct a b (z + b) ≠ 0)
    (hP1 : singleProduct b z ≠ 0) (hP2 : singleProduct b (z + b) ≠ 0)
    (hP3 : singleProduct b (-z) ≠ 0) (hP4 : singleProduct b (b - z) ≠ 0) :
    ellipticGammaSource a b (z + a + b) + ellipticGammaSource a b z
        - ellipticGammaSource a b (z + a) - ellipticGammaSource a b (z + b)
      = -(2 * (Real.pi : ℂ) * Complex.I) := by
  set S : ℂ → ℂ := logDeriv (coneProduct a b) with hS
  set T : ℂ → ℂ := logDeriv (singleProduct b) with hT
  -- the four source values
  have e1 : ellipticGammaSource a b (z + a + b) = -S (-z) - S (z + a + b) := by
    have h := ellipticGammaSource_eq_sub ha hb (z := z + a + b)
      (by rw [show a + b - (z + a + b) = -z by ring]; exact hC1) hC2
    rw [show a + b - (z + a + b) = -z by ring] at h
    exact h
  have e2 : ellipticGammaSource a b z = -S (a + b - z) - S z :=
    ellipticGammaSource_eq_sub ha hb hC3 hC4
  have e3 : ellipticGammaSource a b (z + a) = -S (b - z) - S (z + a) := by
    have h := ellipticGammaSource_eq_sub ha hb (z := z + a)
      (by rw [show a + b - (z + a) = b - z by ring]; exact hC5) hC6
    rw [show a + b - (z + a) = b - z by ring] at h
    exact h
  have e4 : ellipticGammaSource a b (z + b) = -S (a - z) - S (z + b) := by
    have h := ellipticGammaSource_eq_sub ha hb (z := z + b)
      (by rw [show a + b - (z + b) = a - z by ring]; exact hC7) hC8
    rw [show a + b - (z + b) = a - z by ring] at h
    exact h
  -- the `a`-shift law at the four relevant points
  have sa1 : S z = T z + S (z + a) := logDeriv_coneProduct_shift ha hb hP1 hC6
  have sa2 : S (z + b) = T (z + b) + S (z + a + b) := by
    have h := logDeriv_coneProduct_shift ha hb (w := z + b) hP2
      (by rw [show z + b + a = z + a + b by ring]; exact hC2)
    rw [show z + b + a = z + a + b by ring] at h
    exact h
  have sa3 : S (-z) = T (-z) + S (a - z) := by
    have h := logDeriv_coneProduct_shift ha hb (w := -z) hP3
      (by rw [show -z + a = a - z by ring]; exact hC7)
    rw [show -z + a = a - z by ring] at h
    exact h
  have sa4 : S (b - z) = T (b - z) + S (a + b - z) := by
    have h := logDeriv_coneProduct_shift ha hb (w := b - z) hP4
      (by rw [show b - z + a = a + b - z by ring]; exact hC3)
    rw [show b - z + a = a + b - z by ring] at h
    exact h
  -- the `b`-shift law at the two relevant points
  have sb1 : T z = logDeriv (fun x => 1 - expChar x) z + T (z + b) :=
    logDeriv_singleProduct_shift hb hez hP2
  have sb2 : T (-z) = logDeriv (fun x => 1 - expChar x) (-z) + T (b - z) := by
    have h := logDeriv_singleProduct_shift hb (w := -z) hez'
      (by rw [show -z + b = b - z by ring]; exact hP4)
    rw [show -z + b = b - z by ring] at h
    exact h
  -- the two atoms
  have hL1 : logDeriv (fun x => 1 - expChar x) z
      = -(expChar z * (2 * (Real.pi : ℂ) * Complex.I)) / (1 - expChar z) :=
    logDeriv_one_sub_expChar hez
  have hL2 : logDeriv (fun x => 1 - expChar x) (-z)
      = -(expChar (-z) * (2 * (Real.pi : ℂ) * Complex.I)) / (1 - expChar (-z)) :=
    logDeriv_one_sub_expChar hez'
  have hatom := expChar_atom_sum hez hez'
  rw [e1, e2, e3, e4]
  have hcollapse : -S (-z) - S (z + a + b) + (-S (a + b - z) - S z)
      - (-S (b - z) - S (z + a)) - (-S (a - z) - S (z + b))
      = -(logDeriv (fun x => 1 - expChar x) z) - logDeriv (fun x => 1 - expChar x) (-z) := by
    linear_combination -sa1 + sa2 - sa3 + sa4 - sb1 - sb2
  rw [hcollapse, hL1, hL2]
  have hrw : -(-(expChar z * (2 * (Real.pi : ℂ) * Complex.I)) / (1 - expChar z))
      - (-(expChar (-z) * (2 * (Real.pi : ℂ) * Complex.I)) / (1 - expChar (-z)))
      = (2 * (Real.pi : ℂ) * Complex.I)
        * (expChar z / (1 - expChar z) + expChar (-z) / (1 - expChar (-z))) := by
    field_simp
    ring
  rw [hrw, hatom]
  ring

end

end GaloisForLFunctions.HTGeometry
