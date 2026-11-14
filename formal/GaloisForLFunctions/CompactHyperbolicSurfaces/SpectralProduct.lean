import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerTrace
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The spectral Weierstrass product

With `c = a(a − 1)` and `w_j(s) = (s(s − 1) − c)/(λ_j + c)`,

  `E(s) = Π_j (1 + w_j(s)) e^{−w_j(s)}`

converges locally uniformly on `ℂ`, because `Σ_j (λ_j + c)^{−2} < ∞` (`summable_inv_sq`, from the
trace `Σ ν_j < ∞`) and `|(1 + w)e^{−w} − 1| ≤ 3|w|²` for `|w| ≤ 1`.  So `E` is entire
(`differentiable_specProd`), `E(s) = 0` exactly when `λ_j + s(s − 1) = 0` for some `j`
(`specProd_eq_zero_iff`), `E(1 − s) = E(s)` (`specProd_one_sub`), and away from its zeros
`E'/E(s) = Σ_j (2s − 1)(1/(λ_j + s(s−1)) − 1/(λ_j + c))` (`logDeriv_specProd`).
-/

open MeasureTheory Set Real Filter Metric
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

namespace CompactQuotient

variable (X : CompactQuotient) {a : ℝ} (ha : 1 < a)

/-- `w_j(s) = (s(s − 1) − c)/(λ_j + c)`. -/
def specW (j : X.SpecIndex ha) (s : ℂ) : ℂ :=
  (s * (s - 1) - (a * (a - 1) : ℝ)) / ((X.spectralParam ha j + a * (a - 1) : ℝ) : ℂ)

/-- The Weierstrass factor `(1 + w_j) e^{−w_j}`. -/
def specFactor (j : X.SpecIndex ha) (s : ℂ) : ℂ :=
  (1 + X.specW ha j s) * Complex.exp (-X.specW ha j s)

/-- **The spectral product** `E(s) = Π_j (1 + w_j(s)) e^{−w_j(s)}`. -/
def specProd (s : ℂ) : ℂ := ∏' j, X.specFactor ha j s

theorem lam_add_pos (j : X.SpecIndex ha) : 0 < X.spectralParam ha j + a * (a - 1) := by
  have := X.spectralParam_nonneg ha j
  have : 0 < a * (a - 1) := by nlinarith
  linarith

theorem inv_sq_le_mul_sub {l c c' : ℝ} (hl : 0 ≤ l) (hc : 0 < c) (hcc : c < c') :
    1 / (l + c) ^ 2 ≤ c' / ((c' - c) * c) * (1 / (l + c) - 1 / (l + c')) := by
  have h1 : 0 < l + c := by linarith
  have h2 : 0 < l + c' := by linarith
  have hd : 0 < c' - c := by linarith
  have e : c' / ((c' - c) * c) * (1 / (l + c) - 1 / (l + c')) = c' / (c * ((l + c) * (l + c'))) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith [mul_nonneg (mul_nonneg hl hd.le) h1.le]

/-- `Σ_j (λ_j + c)^{−2} < ∞`. -/
theorem summable_inv_sq :
    Summable fun j : X.SpecIndex ha => 1 / (X.spectralParam ha j + a * (a - 1)) ^ 2 := by
  have hsum := (X.hasSum_nu ha (lt_add_one a)).summable
  have hc : 0 < a * (a - 1) := by nlinarith
  have hc' : a * (a - 1) < (a + 1) * (a + 1 - 1) := by nlinarith
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (hsum.mul_left ((a + 1) * (a + 1 - 1) / (((a + 1) * (a + 1 - 1) - a * (a - 1)) * (a * (a - 1)))))
  rw [nu_def]
  exact inv_sq_le_mul_sub (X.spectralParam_nonneg ha j) hc hc'

theorem finite_lam_lt (B : ℝ) : {j : X.SpecIndex ha | X.spectralParam ha j < B}.Finite := by
  have h := (X.summable_inv_sq ha).tendsto_cofinite_zero
  have hB : 0 < 1 / (max B 0 + a * (a - 1)) ^ 2 := by
    have : 0 < a * (a - 1) := by nlinarith
    positivity
  have hev := (tendsto_order.mp h).2 _ hB
  refine (eventually_cofinite.mp hev).subset fun j hj => ?_
  simp only [mem_setOf_eq, not_lt] at hj ⊢
  have h1 := X.lam_add_pos ha j
  have hl := X.spectralParam_nonneg ha j
  apply one_div_le_one_div_of_le (by positivity)
  have : X.spectralParam ha j + a * (a - 1) ≤ max B 0 + a * (a - 1) := by
    have := le_max_left B 0; linarith
  exact pow_le_pow_left₀ h1.le this 2

/-- `‖w_j(s)‖ ≤ (‖s‖² + ‖s‖ + c)/(λ_j + c)`. -/
theorem norm_specW_le (j : X.SpecIndex ha) (s : ℂ) :
    ‖X.specW ha j s‖ ≤ (‖s‖ ^ 2 + ‖s‖ + a * (a - 1)) / (X.spectralParam ha j + a * (a - 1)) := by
  have h1 := X.lam_add_pos ha j
  have hc : 0 < a * (a - 1) := by nlinarith
  rw [specW, norm_div, Complex.norm_real, Real.norm_of_nonneg h1.le]
  refine div_le_div_of_nonneg_right ?_ h1.le
  calc ‖s * (s - 1) - ((a * (a - 1) : ℝ) : ℂ)‖ ≤ ‖s * (s - 1)‖ + ‖((a * (a - 1) : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ ‖s‖ * (‖s‖ + 1) + a * (a - 1) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
        have := norm_sub_le s 1
        rw [norm_one] at this
        nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
    _ = ‖s‖ ^ 2 + ‖s‖ + a * (a - 1) := by ring

/-- `|(1 + w)e^{−w} − 1| ≤ 3|w|²` for `|w| ≤ 1`. -/
theorem norm_weierstrass_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have e : (1 + w) * Complex.exp (-w) - 1 = -(Complex.exp (-w) * (Complex.exp w - 1 - w)) := by
    have : Complex.exp (-w) * Complex.exp w = 1 := by rw [← Complex.exp_add]; simp
    linear_combination this
  rw [e, norm_neg, norm_mul]
  have h1 : ‖Complex.exp (-w)‖ ≤ 3 := by
    rw [Complex.norm_exp]
    have : (-w).re ≤ 1 := by
      have := Complex.abs_re_le_norm (-w)
      rw [norm_neg] at this
      linarith [abs_le.mp this]
    calc Real.exp (-w).re ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have h2 := Complex.norm_exp_sub_one_sub_id_le hw
  calc ‖Complex.exp (-w)‖ * ‖Complex.exp w - 1 - w‖ ≤ 3 * ‖w‖ ^ 2 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)

/-- Uniform bound on a ball for all but finitely many factors. -/
theorem eventually_norm_specFactor_sub_one_le (R : ℝ) :
    ∀ᶠ j in cofinite, ∀ s ∈ ball (0 : ℂ) R, ‖X.specFactor ha j s - 1‖ ≤
      3 * (R ^ 2 + R + a * (a - 1)) ^ 2 * (1 / (X.spectralParam ha j + a * (a - 1)) ^ 2) := by
  have hev : ∀ᶠ j in cofinite, R ^ 2 + R ≤ X.spectralParam ha j :=
    eventually_cofinite.mpr ((X.finite_lam_lt ha _).subset fun j hj => not_le.mp hj)
  refine hev.mono fun j hj s hs => ?_
  have h1 := X.lam_add_pos ha j
  have hs' : ‖s‖ < R := by simpa using hs
  have hR : 0 ≤ R := le_trans (norm_nonneg s) hs'.le
  have hc : 0 < a * (a - 1) := by nlinarith
  have hnum : ‖s‖ ^ 2 + ‖s‖ + a * (a - 1) ≤ R ^ 2 + R + a * (a - 1) := by
    nlinarith [norm_nonneg s]
  have hw : ‖X.specW ha j s‖ ≤ (R ^ 2 + R + a * (a - 1)) / (X.spectralParam ha j + a * (a - 1)) :=
    (X.norm_specW_le ha j s).trans (div_le_div_of_nonneg_right hnum h1.le)
  have hw1 : ‖X.specW ha j s‖ ≤ 1 := hw.trans (by rw [div_le_one h1]; linarith)
  calc ‖X.specFactor ha j s - 1‖ ≤ 3 * ‖X.specW ha j s‖ ^ 2 := norm_weierstrass_sub_one_le hw1
    _ ≤ 3 * ((R ^ 2 + R + a * (a - 1)) / (X.spectralParam ha j + a * (a - 1))) ^ 2 := by
        gcongr
    _ = 3 * (R ^ 2 + R + a * (a - 1)) ^ 2 * (1 / (X.spectralParam ha j + a * (a - 1)) ^ 2) := by
        rw [div_pow, mul_one_div, mul_div_assoc]

theorem multipliableLocallyUniformlyOn_spec (R : ℝ) :
    MultipliableLocallyUniformlyOn (fun j => X.specFactor ha j) (ball (0 : ℂ) R) := by
  have h := ((X.summable_inv_sq ha).mul_left (3 * (R ^ 2 + R + a * (a - 1)) ^ 2)).multipliableLocallyUniformlyOn_one_add
    isOpen_ball (f := fun j s => X.specFactor ha j s - 1)
    (X.eventually_norm_specFactor_sub_one_le ha R) (fun j => by unfold specFactor specW; fun_prop)
  simp only [add_sub_cancel] at h
  exact h

/-- **`E` is entire.** -/
theorem differentiable_specProd : Differentiable ℂ (X.specProd ha) := by
  intro s
  have hmem : s ∈ ball (0 : ℂ) (‖s‖ + 1) := by simp
  have hd : DifferentiableOn ℂ (X.specProd ha) (ball (0 : ℂ) (‖s‖ + 1)) :=
    (X.multipliableLocallyUniformlyOn_spec ha _).hasProdLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun _ => by
        simpa [Finset.prod_fn] using
          DifferentiableOn.finsetProd (fun _ _ => by unfold specFactor specW; fun_prop)) isOpen_ball
  exact (hd s hmem).differentiableAt (isOpen_ball.mem_nhds hmem)

theorem specFactor_eq_zero_iff (j : X.SpecIndex ha) (s : ℂ) :
    X.specFactor ha j s = 0 ↔ (X.spectralParam ha j : ℂ) + s * (s - 1) = 0 := by
  have h1 : ((X.spectralParam ha j + a * (a - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (X.lam_add_pos ha j).ne'
  rw [specFactor, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), specW, add_div' _ _ _ h1,
    div_eq_zero_iff, or_iff_left h1]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem summable_norm_specFactor_sub_one (s : ℂ) :
    Summable fun j => ‖X.specFactor ha j s - 1‖ := by
  refine Summable.of_norm_bounded_eventually
    ((X.summable_inv_sq ha).mul_left (3 * ((‖s‖ + 1) ^ 2 + (‖s‖ + 1) + a * (a - 1)) ^ 2)) ?_
  filter_upwards [X.eventually_norm_specFactor_sub_one_le ha (‖s‖ + 1)] with j hj
  rw [norm_norm]
  exact hj s (by simp)

/-- **The zeros of `E`.** -/
theorem specProd_eq_zero_iff (s : ℂ) :
    X.specProd ha s = 0 ↔ ∃ j : X.SpecIndex ha, (X.spectralParam ha j : ℂ) + s * (s - 1) = 0 := by
  constructor
  · intro h
    by_contra hne
    have hne' : ∀ j, (X.spectralParam ha j : ℂ) + s * (s - 1) ≠ 0 := fun j hj => hne ⟨j, hj⟩
    have h0 := tprod_one_add_ne_zero_of_summable (f := fun j => X.specFactor ha j s - 1)
      (fun j => by
        rw [add_sub_cancel]; exact fun h' => hne' j ((X.specFactor_eq_zero_iff ha j s).mp h'))
      (X.summable_norm_specFactor_sub_one ha s)
    simp only [add_sub_cancel] at h0
    exact h0 h
  · rintro ⟨j, hj⟩
    exact tprod_of_exists_eq_zero ⟨j, (X.specFactor_eq_zero_iff ha j s).mpr hj⟩

/-- **Symmetry.**  `E(1 − s) = E(s)`. -/
theorem specProd_one_sub (s : ℂ) : X.specProd ha (1 - s) = X.specProd ha s := by
  unfold specProd specFactor specW
  congr 1
  funext j
  congr 2 <;> ring_nf

theorem weierstrass_logDeriv_alg {x S c l E : ℂ} (hL : l + c ≠ 0) (hS : l + S ≠ 0) (hE : E ≠ 0) :
    (x / (l + c) * E + (1 + (S - c) / (l + c)) * (E * -(x / (l + c)))) /
      ((1 + (S - c) / (l + c)) * E) = x * (1 / (l + S) - 1 / (l + c)) := by
  have h1 : 1 + (S - c) / (l + c) = (l + S) / (l + c) := by field_simp; ring
  rw [h1]
  field_simp
  ring

theorem logDeriv_specFactor (j : X.SpecIndex ha) {s : ℂ}
    (hs : (X.spectralParam ha j : ℂ) + s * (s - 1) ≠ 0) :
    logDeriv (X.specFactor ha j) s = (2 * s - 1) *
      (1 / ((X.spectralParam ha j : ℂ) + s * (s - 1)) -
        1 / ((X.spectralParam ha j : ℂ) + (a * (a - 1) : ℝ))) := by
  have hLeq : ((X.spectralParam ha j + a * (a - 1) : ℝ) : ℂ) =
      (X.spectralParam ha j : ℂ) + ((a * (a - 1) : ℝ) : ℂ) := by push_cast; ring
  have hL : (X.spectralParam ha j : ℂ) + ((a * (a - 1) : ℝ) : ℂ) ≠ 0 := by
    rw [← hLeq]; exact Complex.ofReal_ne_zero.mpr (X.lam_add_pos ha j).ne'
  have h0 : HasDerivAt (fun s : ℂ => s * (s - 1)) (2 * s - 1) s :=
    ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).congr_deriv (by simp only [id]; ring)
  have hw : HasDerivAt (X.specW ha j)
      ((2 * s - 1) / ((X.spectralParam ha j + a * (a - 1) : ℝ) : ℂ)) s :=
    (h0.sub_const (((a * (a - 1) : ℝ) : ℂ))).div_const _
  have hF : HasDerivAt (X.specFactor ha j) _ s :=
    (hw.const_add 1).mul ((Complex.hasDerivAt_exp _).comp s hw.neg)
  rw [logDeriv_apply, hF.deriv, specFactor, specW, hLeq]
  exact weierstrass_logDeriv_alg hL hs (Complex.exp_ne_zero _)

theorem summable_logDeriv_specFactor {s : ℂ}
    (hs : ∀ j, (X.spectralParam ha j : ℂ) + s * (s - 1) ≠ 0) :
    Summable fun j => logDeriv (X.specFactor ha j) s := by
  simp_rw [fun j => X.logDeriv_specFactor ha j (hs j)]
  set S := s * (s - 1)
  have hc : 0 < a * (a - 1) := by nlinarith
  refine Summable.of_norm_bounded_eventually
    ((X.summable_inv_sq ha).mul_left (2 * ‖2 * s - 1‖ * (‖S‖ + a * (a - 1)))) ?_
  have hev : ∀ᶠ j in cofinite, 2 * ‖S‖ + a * (a - 1) ≤ X.spectralParam ha j :=
    eventually_cofinite.mpr ((X.finite_lam_lt ha _).subset fun j hj => not_le.mp hj)
  refine hev.mono fun j hj => ?_
  have h1 := X.lam_add_pos ha j
  set l := X.spectralParam ha j
  have hlS : (l + a * (a - 1)) / 2 ≤ ‖(l : ℂ) + S‖ := by
    have := norm_sub_norm_le ((l : ℂ)) (-S)
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_of_nonneg
      (X.spectralParam_nonneg ha j)] at this
    linarith
  have hpos : 0 < ‖(l : ℂ) + S‖ := lt_of_lt_of_le (by positivity) hlS
  have heq : (2 * s - 1) * (1 / ((l : ℂ) + S) - 1 / ((l : ℂ) + (a * (a - 1) : ℝ))) =
      (2 * s - 1) * (((a * (a - 1) : ℝ) : ℂ) - S) / (((l : ℂ) + S) * ((l : ℂ) + (a * (a - 1) : ℝ))) := by
    have hne : (l : ℂ) + S ≠ 0 := norm_pos_iff.mp hpos
    have hne' : (l : ℂ) + (a * (a - 1) : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul]
  have hL : ‖(l : ℂ) + ((a * (a - 1) : ℝ) : ℂ)‖ = l + a * (a - 1) := by
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg h1.le]
  rw [hL]
  have hnum : ‖((a * (a - 1) : ℝ) : ℂ) - S‖ ≤ ‖S‖ + a * (a - 1) := by
    have := norm_sub_le (((a * (a - 1) : ℝ) : ℂ)) S
    rw [Complex.norm_real, Real.norm_of_nonneg hc.le] at this
    linarith
  rw [div_le_iff₀ (mul_pos hpos h1)]
  have h2 : 0 < l + a * (a - 1) := h1
  calc ‖2 * s - 1‖ * ‖((a * (a - 1) : ℝ) : ℂ) - S‖
      ≤ ‖2 * s - 1‖ * (‖S‖ + a * (a - 1)) := mul_le_mul_of_nonneg_left hnum (norm_nonneg _)
    _ = 2 * ‖2 * s - 1‖ * (‖S‖ + a * (a - 1)) * (1 / (l + a * (a - 1)) ^ 2) *
          ((l + a * (a - 1)) / 2 * (l + a * (a - 1))) := by field_simp
    _ ≤ 2 * ‖2 * s - 1‖ * (‖S‖ + a * (a - 1)) * (1 / (l + a * (a - 1)) ^ 2) *
          (‖(l : ℂ) + S‖ * (l + a * (a - 1))) := by
        gcongr
    _ = _ := by ring

/-- **The logarithmic derivative of `E`** away from its zeros. -/
theorem logDeriv_specProd {s : ℂ} (hs : ∀ j, (X.spectralParam ha j : ℂ) + s * (s - 1) ≠ 0) :
    logDeriv (X.specProd ha) s = ∑' j, (2 * s - 1) *
      (1 / ((X.spectralParam ha j : ℂ) + s * (s - 1)) -
        1 / ((X.spectralParam ha j : ℂ) + (a * (a - 1) : ℝ))) := by
  have hmem : s ∈ ball (0 : ℂ) (‖s‖ + 1) := by simp
  have hnz : X.specProd ha s ≠ 0 := fun h => by
    obtain ⟨j, hj⟩ := (X.specProd_eq_zero_iff ha s).mp h
    exact hs j hj
  show logDeriv (fun s => ∏' j, X.specFactor ha j s) s = _
  rw [logDeriv_tprod_eq_tsum isOpen_ball hmem
    (fun j h => hs j ((X.specFactor_eq_zero_iff ha j s).mp h))
    (fun j => by unfold specFactor specW; fun_prop)
    (X.summable_logDeriv_specFactor ha hs) (X.multipliableLocallyUniformlyOn_spec ha _) hnz]
  exact tsum_congr fun j => X.logDeriv_specFactor ha j (hs j)

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
