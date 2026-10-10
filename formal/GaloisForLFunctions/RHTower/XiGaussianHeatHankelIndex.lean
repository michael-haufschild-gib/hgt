import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalGramIndex
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalQuadraticLowerLaw

/-!
# Hermite's theorem for the zero heat trace

For a heat time `a > 0` the heat moments `m_n(a) = Σ_q w_q^n e^{-a w_q}` of the squared spectral points
`w_q = z_q²` define the Hankel form on polynomials

`H_a(P, R) = Σ_{k,l} p_k \overline{r_l} m_{k+l}(a) = Σ_q e^{-a w_q} P(w_q) \overline{R(\overline{w_q})}`.

A real frequency contributes `e^{-aλ}|P(λ)|² ≥ 0`; an off-line pair `w, w̄` contributes a rank-two
indefinite form.  Let `U` be the set of squared spectral points with `Im w > 0`, in bijection with the
off-line zero quadruples.

**Theorem** (`exists_heatHankel_negative_subspace`).  For every finite `G ⊆ U` there is a subspace of
`ℂ[X]` of dimension `#G` on which `H_a` is negative definite.  Hence the negative index of `H_a` is
infinite when `U` is infinite (`heatHankel_negative_subspace_of_infinite`), and equals `#U` when `U` is
finite (`heatHankel_negativeIndex_eq_card`): an unconditional analogue of Hermite's count of complex
roots by the signature of a Hankel form.

**Theorem** (`riemannHypothesis_iff_heatHankel_nonneg`).  RH holds iff `H_a` is positive semidefinite.

For the lower bound, `P_u = K · N_u · ((X − ū) + t(X − u))`, where `K` vanishes at every frequency with
`Re w ≤ Λ` outside `G ∪ Ḡ` and `N_u` at `(G ∪ Ḡ) ∖ {u, ū}`.  Low frequencies then contribute exactly
`-|x_u|²|Ω_u|`, while frequencies with `Re w > Λ` cost at most `e^{-aΛ}` times a factor
`(C(1 + |w|))^{2 #K}` relative to `|K(u)|²`.  Since `#K ≪ Λ^{5/8}`, the tail wins for large `Λ`.
-/

open Complex Filter Topology Set Polynomial

namespace RHTower

noncomputable section

/-! ## The Hankel form -/

/-- The contribution `e^{-aw} P(w) \overline{R(w̄)}` of a frequency `w`. -/
def heatHankelTermAt (a : ℝ) (P R : ℂ[X]) (w : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * w) * P.eval w * (starRingEnd ℂ) (R.eval ((starRingEnd ℂ) w))

/-- The heat Hankel form `H_a(P, R) = Σ_q e^{-a w_q} P(w_q) \overline{R(\overline{w_q})}`. -/
def heatHankel (a : ℝ) (P R : ℂ[X]) : ℂ :=
  ∑' q : XiZeroCopy, heatHankelTermAt a P R (xiHeatFrequency q)

/-- The coefficient mass `Σ_k |p_k|`. -/
def polyMass (P : ℂ[X]) : ℝ := P.sum fun _ c => ‖c‖

theorem polyMass_nonneg (P : ℂ[X]) : 0 ≤ polyMass P := by
  rw [polyMass, Polynomial.sum_def]
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_eval_le_polyMass (P : ℂ[X]) (w : ℂ) :
    ‖P.eval w‖ ≤ polyMass P * (1 + ‖w‖) ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum, polyMass, Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖w‖ ^ e ≤ (1 + ‖w‖) ^ e := pow_le_pow_left₀ (norm_nonneg _) (by linarith) e
    _ ≤ (1 + ‖w‖) ^ P.natDegree :=
        pow_le_pow_right₀ (by linarith [norm_nonneg w]) (Polynomial.le_natDegree_of_mem_supp e he)

theorem neg_quarter_lt_re_xiHeatFrequency (q : XiZeroCopy) : -(1 / 4) < (xiHeatFrequency q).re := by
  rw [xiHeatFrequency_re]
  have h := xiSpectralPoint_im_sq_lt_quarter q
  nlinarith [sq_nonneg (xiSpectralPoint q).re]

theorem norm_xiHeatFrequency_le_re (q : XiZeroCopy) :
    ‖xiHeatFrequency q‖ ≤ (xiHeatFrequency q).re + 1 / 2 := by
  have h := xiSpectralPoint_im_sq_lt_quarter q
  have hn : ‖xiHeatFrequency q‖ = (xiSpectralPoint q).re ^ 2 + (xiSpectralPoint q).im ^ 2 := by
    rw [xiHeatFrequency, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn, xiHeatFrequency_re]
  linarith

theorem summable_exp_neg_mul_re_xiHeatFrequency {b : ℝ} (hb : 0 < b) :
    Summable fun q : XiZeroCopy => Real.exp (-(b * (xiHeatFrequency q).re)) := by
  have h := (summable_exp_neg_mul_xiHeatFrequency (τ := (b : ℂ)) (by simpa using hb)).norm
  refine h.congr fun q => ?_
  rw [Complex.norm_exp]
  congr 1
  simp

/-- Polynomial weights are absorbed by half of the heat factor. -/
theorem one_add_norm_pow_mul_exp_le {b : ℝ} (hb : 0 < b) (N : ℕ) (q : XiZeroCopy) :
    (1 + ‖xiHeatFrequency q‖) ^ N * Real.exp (-(2 * b * (xiHeatFrequency q).re)) ≤
      (N.factorial / b ^ N * Real.exp (3 * b / 2)) *
        Real.exp (-(b * (xiHeatFrequency q).re)) := by
  set x := (xiHeatFrequency q).re with hx
  have hx0 : -(1 / 4) < x := neg_quarter_lt_re_xiHeatFrequency q
  have hy : 0 ≤ b * (x + 3 / 2) := mul_nonneg hb.le (by linarith)
  have h1 : (1 + ‖xiHeatFrequency q‖) ^ N ≤ (x + 3 / 2) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith [norm_xiHeatFrequency_le_re q]) N
  have h2 : (x + 3 / 2) ^ N ≤ N.factorial / b ^ N * Real.exp (b * (x + 3 / 2)) := by
    have := Real.pow_div_factorial_le_exp _ hy N
    rw [mul_pow, div_le_iff₀ (by positivity)] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hb N]
  calc (1 + ‖xiHeatFrequency q‖) ^ N * Real.exp (-(2 * b * x))
      ≤ (N.factorial / b ^ N * Real.exp (b * (x + 3 / 2))) * Real.exp (-(2 * b * x)) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _ = (N.factorial / b ^ N * Real.exp (3 * b / 2)) * Real.exp (-(b * x)) := by
        have h3 : Real.exp (b * (x + 3 / 2)) * Real.exp (-(2 * b * x)) =
            Real.exp (3 * b / 2) * Real.exp (-(b * x)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc _ = N.factorial / b ^ N * (Real.exp (b * (x + 3 / 2)) * Real.exp (-(2 * b * x))) := by
              ring
          _ = _ := by rw [h3]; ring

theorem summable_one_add_norm_pow_mul_exp {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Summable fun q : XiZeroCopy =>
      (1 + ‖xiHeatFrequency q‖) ^ N * Real.exp (-(a * (xiHeatFrequency q).re)) := by
  have hb : 0 < a / 2 := by positivity
  refine ((summable_exp_neg_mul_re_xiHeatFrequency hb).mul_left
    (N.factorial / (a / 2) ^ N * Real.exp (3 * (a / 2) / 2))).of_nonneg_of_le
    (fun q => by positivity) fun q => ?_
  have := one_add_norm_pow_mul_exp_le hb N q
  rwa [show 2 * (a / 2) = a by ring] at this

theorem norm_heatHankelTermAt_le (a : ℝ) (P R : ℂ[X]) (q : XiZeroCopy) :
    ‖heatHankelTermAt a P R (xiHeatFrequency q)‖ ≤ polyMass P * polyMass R *
      ((1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + R.natDegree) *
        Real.exp (-(a * (xiHeatFrequency q).re))) := by
  rw [heatHankelTermAt, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp]
  have hre : (-(a : ℂ) * xiHeatFrequency q).re = -(a * (xiHeatFrequency q).re) := by simp
  rw [hre]
  have h1 := norm_eval_le_polyMass P (xiHeatFrequency q)
  have h2 := norm_eval_le_polyMass R ((starRingEnd ℂ) (xiHeatFrequency q))
  rw [Complex.norm_conj] at h2
  have hP := polyMass_nonneg P
  have hR := polyMass_nonneg R
  calc Real.exp (-(a * (xiHeatFrequency q).re)) * ‖P.eval (xiHeatFrequency q)‖ *
        ‖R.eval ((starRingEnd ℂ) (xiHeatFrequency q))‖
      ≤ Real.exp (-(a * (xiHeatFrequency q).re)) *
          (polyMass P * (1 + ‖xiHeatFrequency q‖) ^ P.natDegree) *
          (polyMass R * (1 + ‖xiHeatFrequency q‖) ^ R.natDegree) := by gcongr
    _ = _ := by rw [pow_add]; ring

theorem summable_heatHankelTermAt {a : ℝ} (ha : 0 < a) (P R : ℂ[X]) :
    Summable fun q : XiZeroCopy => heatHankelTermAt a P R (xiHeatFrequency q) :=
  Summable.of_norm (((summable_one_add_norm_pow_mul_exp ha _).mul_left
    (polyMass P * polyMass R)).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_heatHankelTermAt_le a P R))

/-! ## Positivity, the upper bound and RH -/

theorem heatHankelTermAt_conj (a : ℝ) (P : ℂ[X]) (w : ℂ) :
    heatHankelTermAt a P P ((starRingEnd ℂ) w) = (starRingEnd ℂ) (heatHankelTermAt a P P w) := by
  simp only [heatHankelTermAt, map_mul, Complex.conj_conj, ← Complex.exp_conj, map_neg,
    Complex.conj_ofReal]
  ring

theorem re_heatHankelTermAt_of_im_eq_zero (a : ℝ) (P : ℂ[X]) {w : ℂ} (hw : w.im = 0) :
    (heatHankelTermAt a P P w).re = Real.exp (-(a * w.re)) * ‖P.eval w‖ ^ 2 := by
  have hreal : (starRingEnd ℂ) w = w := Complex.conj_eq_iff_im.2 hw
  have hexp : Complex.exp (-(a : ℂ) * w) = ((Real.exp (-(a * w.re)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    apply Complex.ext <;> simp [hw]
  rw [heatHankelTermAt, hreal, hexp, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The Hankel form is nonnegative on polynomials vanishing at the upper frequencies. -/
theorem heatHankel_re_nonneg_of_eval_vanish {a : ℝ} (ha : 0 < a) (P : ℂ[X])
    (hP : ∀ w ∈ xiUpperFrequencies, P.eval w = 0) : 0 ≤ (heatHankel a P P).re := by
  rw [heatHankel, Complex.re_tsum (summable_heatHankelTermAt ha P P)]
  refine tsum_nonneg fun q => ?_
  set w := xiHeatFrequency q with hw
  rcases lt_trichotomy w.im 0 with him | him | him
  · have hc' : P.eval ((starRingEnd ℂ) w) = 0 := by
      refine hP _ ⟨xiZeroCopyLineConjEquiv q, by rw [xiHeatFrequency_lineConj], ?_⟩
      rw [Complex.conj_im]; linarith
    rw [heatHankelTermAt, hc', map_zero, mul_zero, zero_re]
  · rw [re_heatHankelTermAt_of_im_eq_zero a P him]
    positivity
  · rw [heatHankelTermAt, hP w ⟨q, rfl, him⟩, mul_zero, zero_mul, zero_re]

/-- **Upper bound.** -/
theorem finrank_le_of_heatHankel_neg {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite)
    (V : Submodule ℂ ℂ[X]) (hV : ∀ P ∈ V, P ≠ 0 → (heatHankel a P P).re < 0) :
    Module.finrank ℂ V ≤ hU.toFinset.card := by
  classical
  set L : ℂ[X] →ₗ[ℂ] (hU.toFinset → ℂ) := LinearMap.pi fun w => Polynomial.leval (w : ℂ) with hL
  have hinj : Function.Injective (L.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    by_contra hne
    have hP0 : (P : ℂ[X]) ≠ 0 := fun h => hne (Subtype.ext h)
    have hvan : ∀ w ∈ xiUpperFrequencies, (P : ℂ[X]).eval w = 0 := by
      intro w hw
      have := congrFun hP ⟨w, hU.mem_toFinset.2 hw⟩
      simpa [hL] using this
    have h1 := heatHankel_re_nonneg_of_eval_vanish ha (P : ℂ[X]) hvan
    have h2 := hV P P.2 hP0
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

theorem heatHankel_re_nonneg_of_riemannHypothesis {a : ℝ} (ha : 0 < a) (hRH : RiemannHypothesis)
    (P : ℂ[X]) : 0 ≤ (heatHankel a P P).re := by
  refine heatHankel_re_nonneg_of_eval_vanish ha P fun w hw => ?_
  exfalso
  obtain ⟨q, rfl, him⟩ := hw
  have h0 : (xiSpectralPoint q).im = 0 :=
    (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH q
  rw [xiHeatFrequency_im, h0, mul_zero] at him
  exact lt_irrefl 0 him

/-! ## Assembly of a negative-definite family -/

theorem eval_sum_smul {ι : Type*} [Fintype ι] (P : ι → ℂ[X]) (x : ι → ℂ) (w : ℂ) :
    (∑ i, x i • P i).eval w = ∑ i, x i * (P i).eval w := by
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_smul, smul_eq_mul]

/-- **Localization.**  If every polynomial but `P v` vanishes at `w` and `w̄`, the frequency `w` sees
only the `v`-component. -/
theorem heatHankelTermAt_sum_eq_of_vanish {ι : Type*} [Fintype ι] (a : ℝ) (P : ι → ℂ[X])
    (x : ι → ℂ) (v : ι) (w : ℂ)
    (hvan : ∀ i, i ≠ v → (P i).eval w = 0 ∧ (P i).eval ((starRingEnd ℂ) w) = 0) :
    heatHankelTermAt a (∑ i, x i • P i) (∑ i, x i • P i) w =
      ((‖x v‖ ^ 2 : ℝ) : ℂ) * heatHankelTermAt a (P v) (P v) w := by
  have h1 : (∑ i, x i • P i).eval w = x v * (P v).eval w := by
    rw [eval_sum_smul, Finset.sum_eq_single v]
    · intro i _ hi; rw [(hvan i hi).1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  have h2 : (∑ i, x i • P i).eval ((starRingEnd ℂ) w) = x v * (P v).eval ((starRingEnd ℂ) w) := by
    rw [eval_sum_smul, Finset.sum_eq_single v]
    · intro i _ hi; rw [(hvan i hi).2, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  have hx : x v * (starRingEnd ℂ) (x v) = ((‖x v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [heatHankelTermAt, heatHankelTermAt, h1, h2, map_mul]
  linear_combination (Complex.exp (-(a : ℂ) * w) * (P v).eval w *
    (starRingEnd ℂ) ((P v).eval ((starRingEnd ℂ) w))) * hx

/-- The tail contribution `e^{-aw}(|P(w)|² + |P(w̄)|²)` of frequencies with `Re w > Λ`. -/
def heatHankelTail (a Λ : ℝ) (P : ℂ[X]) (q : XiZeroCopy) : ℝ :=
  if Λ < (xiHeatFrequency q).re then Real.exp (-(a * (xiHeatFrequency q).re)) *
    (‖P.eval (xiHeatFrequency q)‖ ^ 2 + ‖P.eval ((starRingEnd ℂ) (xiHeatFrequency q))‖ ^ 2)
  else 0

theorem heatHankelTail_nonneg (a Λ : ℝ) (P : ℂ[X]) (q : XiZeroCopy) :
    0 ≤ heatHankelTail a Λ P q := by
  unfold heatHankelTail
  split_ifs
  · positivity
  · exact le_rfl

theorem summable_heatHankelTail {a : ℝ} (ha : 0 < a) (Λ : ℝ) (P : ℂ[X]) :
    Summable (heatHankelTail a Λ P) := by
  refine ((summable_one_add_norm_pow_mul_exp ha (2 * P.natDegree)).mul_left
    (2 * polyMass P ^ 2)).of_nonneg_of_le (heatHankelTail_nonneg a Λ P) fun q => ?_
  unfold heatHankelTail
  split_ifs
  · have h1 := norm_eval_le_polyMass P (xiHeatFrequency q)
    have h2 := norm_eval_le_polyMass P ((starRingEnd ℂ) (xiHeatFrequency q))
    rw [Complex.norm_conj] at h2
    have hm := polyMass_nonneg P
    have hw : 0 ≤ (1 + ‖xiHeatFrequency q‖) ^ P.natDegree := by positivity
    have h1' : ‖P.eval (xiHeatFrequency q)‖ ^ 2 ≤ (polyMass P * (1 + ‖xiHeatFrequency q‖) ^ P.natDegree) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖P.eval ((starRingEnd ℂ) (xiHeatFrequency q))‖ ^ 2 ≤
        (polyMass P * (1 + ‖xiHeatFrequency q‖) ^ P.natDegree) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc Real.exp (-(a * (xiHeatFrequency q).re)) *
          (‖P.eval (xiHeatFrequency q)‖ ^ 2 + ‖P.eval ((starRingEnd ℂ) (xiHeatFrequency q))‖ ^ 2)
        ≤ Real.exp (-(a * (xiHeatFrequency q).re)) *
            (2 * (polyMass P * (1 + ‖xiHeatFrequency q‖) ^ P.natDegree) ^ 2) := by
          gcongr
          linarith
      _ = 2 * polyMass P ^ 2 * ((1 + ‖xiHeatFrequency q‖) ^ (2 * P.natDegree) *
            Real.exp (-(a * (xiHeatFrequency q).re))) := by ring
  · positivity

/-- **Assembly.**  Polynomials `P_i` attached to distinct upper frequencies `u_i` with
`Re u_i ≤ Λ`, vanishing at every frequency with real part `≤ Λ` other than the `u_j, ū_j`, vanishing at
`u_j, ū_j` for `j ≠ i`, and with rank-two value `-Ω_i` at `u_i`, satisfy
`Re H_a(Σ x_i P_i) ≤ Σ_i |x_i|² (#ι/2 · Σ_q tail_i(q) − Ω_i)`. -/
theorem re_heatHankel_sum_le {a : ℝ} (ha : 0 < a) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → ℂ[X]) (u : ι → ℂ) (qs : ι → XiZeroCopy) (Ω : ι → ℝ) {Λ : ℝ}
    (hqs : ∀ i, xiHeatFrequency (qs i) = u i) (hu : ∀ i, 0 < (u i).im)
    (huinj : Function.Injective u) (hΛ : ∀ i, (u i).re ≤ Λ)
    (hlow : ∀ q : XiZeroCopy, (xiHeatFrequency q).re ≤ Λ →
      (∀ i, xiHeatFrequency q ≠ u i ∧ xiHeatFrequency q ≠ (starRingEnd ℂ) (u i)) →
      ∀ i, (P i).eval (xiHeatFrequency q) = 0 ∧
        (P i).eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0)
    (hvan : ∀ i j, i ≠ j → (P i).eval (u j) = 0 ∧ (P i).eval ((starRingEnd ℂ) (u j)) = 0)
    (hval : ∀ i, heatHankelTermAt a (P i) (P i) (u i) = -((Ω i : ℝ) : ℂ)) (hΩ : ∀ i, 0 ≤ Ω i)
    (x : ι → ℂ) :
    (heatHankel a (∑ i, x i • P i) (∑ i, x i • P i)).re ≤
      ∑ i, ‖x i‖ ^ 2 * (Fintype.card ι / 2 * (∑' q : XiZeroCopy, heatHankelTail a Λ (P i) q) -
        Ω i) := by
  classical
  set c := ∑ i, x i • P i with hc
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  -- the conjugate-frequency values
  have hvalc : ∀ i, heatHankelTermAt a (P i) (P i) ((starRingEnd ℂ) (u i)) = -((Ω i : ℝ) : ℂ) := by
    intro i
    rw [heatHankelTermAt_conj, hval i, map_neg, Complex.conj_ofReal]
  -- termwise bound
  have hterm : ∀ q : XiZeroCopy, (heatHankelTermAt a c c (xiHeatFrequency q)).re ≤
      ∑ i, ‖x i‖ ^ 2 * (m / 2 * heatHankelTail a Λ (P i) q - if q = qs i then Ω i else 0) := by
    intro q
    set w := xiHeatFrequency q with hw
    by_cases hlo : w.re ≤ Λ
    · have htail0 : ∀ i, heatHankelTail a Λ (P i) q = 0 := fun i => by
        unfold heatHankelTail; rw [if_neg (not_lt.2 hlo)]
      simp only [htail0, mul_zero, zero_sub]
      by_cases hhit : ∃ v, w = u v ∨ w = (starRingEnd ℂ) (u v)
      · obtain ⟨v, hv⟩ := hhit
        have hvan' : ∀ i, i ≠ v → (P i).eval w = 0 ∧ (P i).eval ((starRingEnd ℂ) w) = 0 := by
          intro i hi
          rcases hv with hv | hv
          · rw [hv]; exact hvan i v hi
          · rw [hv, Complex.conj_conj]; exact ⟨(hvan i v hi).2, (hvan i v hi).1⟩
        have hloc := heatHankelTermAt_sum_eq_of_vanish a P x v w hvan'
        have hvalw : heatHankelTermAt a (P v) (P v) w = -((Ω v : ℝ) : ℂ) := by
          rcases hv with hv | hv
          · rw [hv]; exact hval v
          · rw [hv]; exact hvalc v
        rw [hloc, hvalw, re_ofReal_mul, neg_re, ofReal_re]
        have hrest : ∀ i, i ≠ v → (if q = qs i then Ω i else 0) = 0 := by
          intro i hi
          rw [if_neg]
          intro hqi
          have h1 := hqs i
          rw [← hqi] at h1
          rcases hv with hv | hv
          · exact hi (huinj (by rw [← h1, ← hv]))
          · have h2 := hu i
            rw [← h1, ← hw, hv, Complex.conj_im] at h2
            linarith [hu v]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
        have hzero : ∑ i ∈ Finset.univ.erase v,
            ‖x i‖ ^ 2 * -(if q = qs i then Ω i else 0) = 0 :=
          Finset.sum_eq_zero fun i hi => by rw [hrest i (Finset.ne_of_mem_erase hi), neg_zero, mul_zero]
        rw [hzero, add_zero]
        have hv' : (if q = qs v then Ω v else 0) ≤ Ω v := by
          split_ifs
          · exact le_rfl
          · exact hΩ v
        exact mul_le_mul_of_nonneg_left (neg_le_neg hv') (sq_nonneg _)
      · push Not at hhit
        have hz : ∀ i, (P i).eval w = 0 ∧ (P i).eval ((starRingEnd ℂ) w) = 0 :=
          hlow q hlo fun i => hhit i
        have hc0 : heatHankelTermAt a c c w = 0 := by
          rw [heatHankelTermAt, hc, eval_sum_smul]
          simp [(hz _).1]
        rw [hc0, zero_re]
        refine Finset.sum_nonneg fun i _ => ?_
        rw [if_neg]
        · simp
        · intro hqi
          have h1 := hqs i
          rw [← hqi] at h1
          exact (hhit i).1 (by rw [hw, h1])
    · push Not at hlo
      have hne : ∀ i, q ≠ qs i := fun i hqi => by
        have h1 := hqs i
        rw [← hqi] at h1
        have := hΛ i
        rw [← h1] at this
        linarith
      simp only [hne, if_false, sub_zero]
      have htail : ∀ i, heatHankelTail a Λ (P i) q = Real.exp (-(a * w.re)) *
          (‖(P i).eval w‖ ^ 2 + ‖(P i).eval ((starRingEnd ℂ) w)‖ ^ 2) := fun i => by
        unfold heatHankelTail; rw [if_pos hlo]
      simp only [htail]
      have hnorm : ‖heatHankelTermAt a c c w‖ = Real.exp (-(a * w.re)) *
          ‖c.eval w‖ * ‖c.eval ((starRingEnd ℂ) w)‖ := by
        rw [heatHankelTermAt, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp]
        congr 2
        simp
      have hsq : ∀ z : ℂ, ‖(∑ i, x i • P i).eval z‖ ^ 2 ≤
          m * ∑ i, ‖x i‖ ^ 2 * ‖(P i).eval z‖ ^ 2 := by
        intro z
        rw [eval_sum_smul]
        have h1 : ‖∑ i, x i * (P i).eval z‖ ≤ ∑ i, ‖x i‖ * ‖(P i).eval z‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
        have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
          (f := fun i => ‖x i‖ * ‖(P i).eval z‖)
        rw [Finset.card_univ] at h2
        calc ‖∑ i, x i * (P i).eval z‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖(P i).eval z‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ ≤ m * ∑ i, (‖x i‖ * ‖(P i).eval z‖) ^ 2 := h2
          _ = m * ∑ i, ‖x i‖ ^ 2 * ‖(P i).eval z‖ ^ 2 := by simp only [mul_pow]
      have hA := hsq w
      have hB := hsq ((starRingEnd ℂ) w)
      have hamgm : ‖c.eval w‖ * ‖c.eval ((starRingEnd ℂ) w)‖ ≤
          (‖c.eval w‖ ^ 2 + ‖c.eval ((starRingEnd ℂ) w)‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖c.eval w‖ - ‖c.eval ((starRingEnd ℂ) w)‖)]
      have he := (Real.exp_pos (-(a * w.re))).le
      calc (heatHankelTermAt a c c w).re ≤ ‖heatHankelTermAt a c c w‖ := Complex.re_le_norm _
        _ = Real.exp (-(a * w.re)) * (‖c.eval w‖ * ‖c.eval ((starRingEnd ℂ) w)‖) := by
            rw [hnorm, mul_assoc]
        _ ≤ Real.exp (-(a * w.re)) *
            ((m * ∑ i, ‖x i‖ ^ 2 * ‖(P i).eval w‖ ^ 2 +
              m * ∑ i, ‖x i‖ ^ 2 * ‖(P i).eval ((starRingEnd ℂ) w)‖ ^ 2) / 2) := by
            refine mul_le_mul_of_nonneg_left (hamgm.trans ?_) he
            linarith
        _ = ∑ i, ‖x i‖ ^ 2 * (m / 2 * (Real.exp (-(a * w.re)) *
            (‖(P i).eval w‖ ^ 2 + ‖(P i).eval ((starRingEnd ℂ) w)‖ ^ 2))) := by
            rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
  -- summation
  have hsT : ∀ i, Summable (heatHankelTail a Λ (P i)) := fun i => summable_heatHankelTail ha Λ (P i)
  have hg : ∀ i, Summable fun q : XiZeroCopy =>
      ‖x i‖ ^ 2 * (m / 2 * heatHankelTail a Λ (P i) q - if q = qs i then Ω i else 0) :=
    fun i => (((hsT i).mul_left _).sub (hasSum_ite_eq (qs i) (Ω i)).summable).mul_left _
  have hsre : Summable fun q : XiZeroCopy => (heatHankelTermAt a c c (xiHeatFrequency q)).re :=
    (summable_heatHankelTermAt ha c c).mapL Complex.reCLM
  rw [heatHankel, Complex.re_tsum (summable_heatHankelTermAt ha c c)]
  refine (Summable.tsum_le_tsum hterm hsre (summable_sum fun i _ => hg i)).trans (le_of_eq ?_)
  rw [Summable.tsum_finsetSum fun i _ => hg i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, Summable.tsum_sub ((hsT i).mul_left _) (hasSum_ite_eq (qs i) (Ω i)).summable,
    tsum_mul_left, (hasSum_ite_eq (qs i) (Ω i)).tsum_eq]

/-! ## Frequencies below a level, root polynomials, and the tail -/

/-- The squared spectral points with real part at most `Λ`. -/
def heatFrequenciesBelow (Λ : ℝ) : Finset ℂ :=
  ((xiCopiesBelow (Real.sqrt (Λ + 1))).filter fun q => (xiHeatFrequency q).re ≤ Λ).image
    xiHeatFrequency

theorem mem_heatFrequenciesBelow {Λ : ℝ} {v : ℂ} :
    v ∈ heatFrequenciesBelow Λ ↔ ∃ q : XiZeroCopy, xiHeatFrequency q = v ∧ v.re ≤ Λ := by
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨q, rfl, (Finset.mem_filter.1 hq).2⟩
  · rintro ⟨q, rfl, hle⟩
    refine Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨?_, hle⟩, rfl⟩
    rw [mem_xiCopiesBelow, zeroOrdinate, ← xiSpectralPoint_re_eq]
    apply Real.abs_le_sqrt
    have hre := xiHeatFrequency_re q
    have him := xiSpectralPoint_im_sq_lt_quarter q
    nlinarith

theorem conj_mem_heatFrequenciesBelow {Λ : ℝ} {v : ℂ} (hv : v ∈ heatFrequenciesBelow Λ) :
    (starRingEnd ℂ) v ∈ heatFrequenciesBelow Λ := by
  obtain ⟨q, rfl, hle⟩ := mem_heatFrequenciesBelow.1 hv
  exact mem_heatFrequenciesBelow.2 ⟨xiZeroCopyLineConjEquiv q, xiHeatFrequency_lineConj q,
    by rw [Complex.conj_re]; exact hle⟩

/-- At most `D (Λ + 7)^{5/8}` frequencies have real part `≤ Λ`. -/
theorem exists_card_heatFrequenciesBelow_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ Λ : ℝ, 0 ≤ Λ →
      ((heatFrequenciesBelow Λ).card : ℝ) ≤ D * (Λ + 7) ^ (5 / 8 : ℝ) := by
  set D₀ : ℝ := 20 * (|xiLineTwoLogDerivConstant| + 4) + 1 with hD₀
  have hD₀0 : 0 ≤ D₀ := by rw [hD₀]; positivity
  refine ⟨D₀ * 11 ^ (5 / 8 : ℝ), by positivity, fun Λ hΛ => ?_⟩
  have hΓ : 0 ≤ Real.sqrt (Λ + 1) := Real.sqrt_nonneg _
  have h1 : ((heatFrequenciesBelow Λ).card : ℝ) ≤ (xiCopiesBelow (Real.sqrt (Λ + 1))).card := by
    exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le _ _))
  have h2 := card_xiCopiesBelow_add_one_le hΓ
  have h3 : (Real.sqrt (Λ + 1) + 6) ^ (5 / 4 : ℝ) ≤ 11 ^ (5 / 8 : ℝ) * (Λ + 7) ^ (5 / 8 : ℝ) := by
    have hsq : (Real.sqrt (Λ + 1) + 6) ^ 2 ≤ 11 * (Λ + 7) := by
      have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ Λ + 1)
      nlinarith [sq_nonneg (Real.sqrt (Λ + 1) - 1)]
    have hpos : 0 ≤ Real.sqrt (Λ + 1) + 6 := by positivity
    calc (Real.sqrt (Λ + 1) + 6) ^ (5 / 4 : ℝ) =
          ((Real.sqrt (Λ + 1) + 6) ^ (2 : ℕ)) ^ (5 / 8 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hpos]; norm_num
      _ ≤ (11 * (Λ + 7)) ^ (5 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hsq (by norm_num)
      _ = 11 ^ (5 / 8 : ℝ) * (Λ + 7) ^ (5 / 8 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
  calc ((heatFrequenciesBelow Λ).card : ℝ) ≤ (xiCopiesBelow (Real.sqrt (Λ + 1))).card := h1
    _ ≤ D₀ * (Real.sqrt (Λ + 1) + 6) ^ (5 / 4 : ℝ) := by linarith
    _ ≤ D₀ * (11 ^ (5 / 8 : ℝ) * (Λ + 7) ^ (5 / 8 : ℝ)) := mul_le_mul_of_nonneg_left h3 hD₀0
    _ = D₀ * 11 ^ (5 / 8 : ℝ) * (Λ + 7) ^ (5 / 8 : ℝ) := by ring

/-- A positive separation between `G` and the points of `S` other than `u, ū`. -/
theorem exists_pos_le_norm_sub (G S : Finset ℂ) :
    ∃ d : ℝ, 0 < d ∧ ∀ u ∈ G, ∀ v ∈ S, v ≠ u → v ≠ (starRingEnd ℂ) u → d ≤ ‖u - v‖ := by
  classical
  set D := (G ×ˢ S).filter fun p : ℂ × ℂ => p.2 ≠ p.1 ∧ p.2 ≠ (starRingEnd ℂ) p.1 with hD
  by_cases hne : D.Nonempty
  · obtain ⟨p, hp, hmin⟩ := D.exists_min_image (fun p : ℂ × ℂ => ‖p.1 - p.2‖) hne
    have hp' := Finset.mem_filter.1 hp
    refine ⟨‖p.1 - p.2‖, norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hp'.2.1)),
      fun u hu v hv h1 h2 => ?_⟩
    exact hmin (u, v) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hu, hv⟩, h1, h2⟩)
  · refine ⟨1, one_pos, fun u hu v hv h1 h2 => absurd ⟨(u, v),
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hu, hv⟩, h1, h2⟩⟩ hne⟩

/-- `∏_{v ∈ S} (X − v)`. -/
def heatRootPoly (S : Finset ℂ) : ℂ[X] := ∏ v ∈ S, (X - C v)

theorem eval_heatRootPoly (S : Finset ℂ) (w : ℂ) : (heatRootPoly S).eval w = ∏ v ∈ S, (w - v) := by
  rw [heatRootPoly, Polynomial.eval_prod]
  simp

theorem eval_heatRootPoly_eq_zero {S : Finset ℂ} {v : ℂ} (hv : v ∈ S) : (heatRootPoly S).eval v = 0 := by
  rw [eval_heatRootPoly]
  exact Finset.prod_eq_zero hv (sub_self v)

theorem eval_heatRootPoly_ne_zero {S : Finset ℂ} {w : ℂ} (hw : w ∉ S) : (heatRootPoly S).eval w ≠ 0 := by
  rw [eval_heatRootPoly]
  exact Finset.prod_ne_zero_iff.2 fun v hv => sub_ne_zero.2 fun h => hw (h ▸ hv)

theorem eval_heatRootPoly_conj {S : Finset ℂ} (hS : ∀ v ∈ S, (starRingEnd ℂ) v ∈ S) (w : ℂ) :
    (heatRootPoly S).eval ((starRingEnd ℂ) w) = (starRingEnd ℂ) ((heatRootPoly S).eval w) := by
  rw [eval_heatRootPoly, eval_heatRootPoly, map_prod]
  refine Finset.prod_nbij' (fun v => (starRingEnd ℂ) v) (fun v => (starRingEnd ℂ) v)
    (fun v hv => hS v hv) (fun v hv => hS v hv) (fun v _ => Complex.conj_conj v)
    (fun v _ => Complex.conj_conj v) fun v _ => ?_
  rw [map_sub, Complex.conj_conj]

theorem norm_eval_heatRootPoly_le {S : Finset ℂ} {u w : ℂ} {C₀ : ℝ}
    (h : ∀ v ∈ S, ‖w - v‖ ≤ C₀ * (1 + ‖w‖) * ‖u - v‖) :
    ‖(heatRootPoly S).eval w‖ ≤ (C₀ * (1 + ‖w‖)) ^ S.card * ‖(heatRootPoly S).eval u‖ := by
  rw [eval_heatRootPoly, eval_heatRootPoly, norm_prod, norm_prod, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun v _ => norm_nonneg _) h

/-- A root `v` is either far from `u`, or `d`-separated from it. -/
theorem norm_sub_le_of_far_or_sep {u v w : ℂ} {d R : ℝ} (hd : 0 < d) (hu : ‖u‖ ≤ R)
    (hsep : ‖v‖ < 2 * R + 2 → d ≤ ‖u - v‖) :
    ‖w - v‖ ≤ (2 + (2 * R + 3) / d) * (1 + ‖w‖) * ‖u - v‖ := by
  have hR : 0 ≤ R := (norm_nonneg u).trans hu
  have hw0 := norm_nonneg w
  have huv0 := norm_nonneg (u - v)
  have hq : 0 ≤ (2 * R + 3) / d := by positivity
  by_cases hv : ‖v‖ < 2 * R + 2
  · have h1 := hsep hv
    have h2 : ‖w - v‖ ≤ (2 * R + 3) * (1 + ‖w‖) := by
      calc ‖w - v‖ ≤ ‖w‖ + ‖v‖ := norm_sub_le _ _
        _ ≤ (2 * R + 3) * (1 + ‖w‖) := by nlinarith
    have h3 : 2 * R + 3 ≤ (2 * R + 3) / d * ‖u - v‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ‖w - v‖ ≤ (2 * R + 3) * (1 + ‖w‖) := h2
      _ ≤ (2 * R + 3) / d * ‖u - v‖ * (1 + ‖w‖) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ (2 + (2 * R + 3) / d) * (1 + ‖w‖) * ‖u - v‖ := by nlinarith
  · push Not at hv
    have h1 : ‖v‖ ≤ 2 * ‖u - v‖ := by
      have := norm_sub_norm_le v u
      rw [norm_sub_rev] at this
      linarith
    have h2 : ‖w - v‖ ≤ (1 + ‖w‖) * ‖v‖ := by
      calc ‖w - v‖ ≤ ‖w‖ + ‖v‖ := norm_sub_le _ _
        _ ≤ (1 + ‖w‖) * ‖v‖ := by nlinarith
    calc ‖w - v‖ ≤ (1 + ‖w‖) * ‖v‖ := h2
      _ ≤ (1 + ‖w‖) * (2 * ‖u - v‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (2 + (2 * R + 3) / d) * (1 + ‖w‖) * ‖u - v‖ := by
          have := mul_nonneg (mul_nonneg hq (by positivity : (0 : ℝ) ≤ 1 + ‖w‖)) huv0
          nlinarith

/-- `E (x + 7)^{7/8} + |L| ≤ κ x` for all large `x`. -/
theorem exists_threshold_seven_eighths {κ E L : ℝ} (hκ : 0 < κ) (hE : 0 ≤ E) :
    ∃ X : ℝ, 7 ≤ X ∧ ∀ x : ℝ, X ≤ x → E * (x + 7) ^ (7 / 8 : ℝ) + |L| ≤ κ * x := by
  set Y := ((2 * E + |L|) / κ) ^ (8 : ℕ) with hY
  refine ⟨max 7 Y, le_max_left _ _, fun x hx => ?_⟩
  have hx7 : 7 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have h1 : (x + 7) ^ (7 / 8 : ℝ) ≤ 2 * x ^ (7 / 8 : ℝ) := by
    calc (x + 7) ^ (7 / 8 : ℝ) ≤ (2 * x) ^ (7 / 8 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 ^ (7 / 8 : ℝ) * x ^ (7 / 8 : ℝ) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ (7 / 8 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (7 / 8 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hx1 : 1 ≤ x ^ (7 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hb : 0 ≤ (2 * E + |L|) / κ := by positivity
  have h2 : (2 * E + |L|) / κ ≤ x ^ (1 / 8 : ℝ) := by
    have hYx : Y ≤ x := (le_max_right _ _).trans hx
    calc (2 * E + |L|) / κ = (((2 * E + |L|) / κ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb]; norm_num
      _ ≤ x ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hYx (by norm_num)
  have hL := abs_nonneg L
  calc E * (x + 7) ^ (7 / 8 : ℝ) + |L| ≤ E * (2 * x ^ (7 / 8 : ℝ)) + |L| * x ^ (7 / 8 : ℝ) := by
        gcongr
        nlinarith
    _ = (2 * E + |L|) / κ * κ * x ^ (7 / 8 : ℝ) := by field_simp
    _ ≤ x ^ (1 / 8 : ℝ) * κ * x ^ (7 / 8 : ℝ) := by gcongr
    _ = κ * (x ^ (1 / 8 : ℝ) * x ^ (7 / 8 : ℝ)) := by ring
    _ = κ * x := by rw [← Real.rpow_add hx0]; norm_num

/-- The heat tail beyond a large level is small, uniformly over `#K ≤ D (Λ + 7)^{5/8}`. -/
theorem exists_level_tail_small {a : ℝ} (ha : 0 < a) {C₀ D : ℝ} (hC₀ : 1 ≤ C₀) (hD : 0 ≤ D)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : ℝ) :
    ∃ Λ : ℝ, Λ₀ ≤ Λ ∧ 0 ≤ Λ ∧ ∀ k : ℕ, (k : ℝ) ≤ D * (Λ + 7) ^ (5 / 8 : ℝ) →
      ∑' q : XiZeroCopy, (if Λ < (xiHeatFrequency q).re then
        Real.exp (-(a * (xiHeatFrequency q).re)) *
          ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ N)
        else 0) ≤ ε := by
  have ha2 : 0 < a / 2 := by positivity
  set S := ∑' q : XiZeroCopy, Real.exp (-(a / 2 * (xiHeatFrequency q).re)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
  set η := ε / (S + 1) with hη
  have hη0 : 0 < η := by positivity
  set E := (2 * D + N) * (C₀ + 4) with hE
  have hE0 : 0 ≤ E := by positivity
  obtain ⟨X, hX7, hX⟩ := exists_threshold_seven_eighths (L := Real.log η) ha2 hE0
  refine ⟨max (max Λ₀ 0) X, (le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _), fun k hk => ?_⟩
  set Λ := max (max Λ₀ 0) X with hΛ
  have hΛ0 : 0 ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  have hΛX : X ≤ Λ := le_max_right _ _
  have hpt : ∀ q : XiZeroCopy, (if Λ < (xiHeatFrequency q).re then
      Real.exp (-(a * (xiHeatFrequency q).re)) *
        ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ N) else 0) ≤
      η * Real.exp (-(a / 2 * (xiHeatFrequency q).re)) := by
    intro q
    split_ifs with hq
    · set x := (xiHeatFrequency q).re with hx
      have hx0 : 0 < x := by linarith
      have hxX : X ≤ x := hΛX.trans hq.le
      have hw := norm_xiHeatFrequency_le_re q
      rw [← hx] at hw
      set y := C₀ * (x + 7) with hy
      have hy1 : 1 ≤ y := by rw [hy]; nlinarith
      have hb1 : C₀ * (1 + ‖xiHeatFrequency q‖) ≤ y := by
        rw [hy]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have hb2 : 1 + ‖xiHeatFrequency q‖ ≤ y := by
        rw [hy]; nlinarith [norm_nonneg (xiHeatFrequency q)]
      have hprod : (C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ N ≤
          y ^ (2 * k + N) := by
        rw [pow_add]
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hb1 _)
          (pow_le_pow_left₀ (by positivity) hb2 _) (by positivity) (by positivity)
      -- the exponent
      have hlog : Real.log y ≤ (C₀ + 4) * (x + 7) ^ (1 / 4 : ℝ) := by
        have h1 : Real.log y = Real.log C₀ + Real.log (x + 7) := by
          rw [hy, Real.log_mul (by linarith) (by linarith)]
        have h2 : Real.log C₀ ≤ C₀ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
        have h3 : Real.log (x + 7) ≤ (x + 7) ^ (1 / 4 : ℝ) / (1 / 4) :=
          Real.log_le_rpow_div (by linarith) (by norm_num)
        have h4 : 1 ≤ (x + 7) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
        rw [h1]
        nlinarith
      have hM : ((2 * k + N : ℕ) : ℝ) ≤ (2 * D + N) * (x + 7) ^ (5 / 8 : ℝ) := by
        have h1 : (Λ + 7) ^ (5 / 8 : ℝ) ≤ (x + 7) ^ (5 / 8 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        have h2 : 1 ≤ (x + 7) ^ (5 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
        push_cast
        nlinarith
      have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      have hexp : ((2 * k + N : ℕ) : ℝ) * Real.log y ≤ E * (x + 7) ^ (7 / 8 : ℝ) := by
        have hsplit : (x + 7) ^ (7 / 8 : ℝ) = (x + 7) ^ (5 / 8 : ℝ) * (x + 7) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add (by linarith)]; norm_num
        rw [hsplit, hE]
        have h5 : 0 ≤ (x + 7) ^ (5 / 8 : ℝ) := by positivity
        calc ((2 * k + N : ℕ) : ℝ) * Real.log y
            ≤ (2 * D + N) * (x + 7) ^ (5 / 8 : ℝ) * ((C₀ + 4) * (x + 7) ^ (1 / 4 : ℝ)) :=
              mul_le_mul hM hlog hlogy0 (by positivity)
          _ = (2 * D + N) * (C₀ + 4) * ((x + 7) ^ (5 / 8 : ℝ) * (x + 7) ^ (1 / 4 : ℝ)) := by ring
      have hthr := hX x hxX
      have hpowy : y ^ (2 * k + N) ≤ η * Real.exp (a / 2 * x) := by
        rw [← Real.exp_log (by linarith : 0 < y), ← Real.exp_nat_mul, ← Real.exp_log hη0,
          ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have := neg_abs_le (Real.log η)
        linarith
      calc Real.exp (-(a * x)) *
            ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ N)
          ≤ Real.exp (-(a * x)) * (η * Real.exp (a / 2 * x)) :=
            mul_le_mul_of_nonneg_left (hprod.trans hpowy) (Real.exp_pos _).le
        _ = η * Real.exp (-(a / 2 * x)) := by
            rw [mul_left_comm, ← Real.exp_add]
            congr 2
            ring
    · positivity
  have hsum : Summable fun q : XiZeroCopy => η * Real.exp (-(a / 2 * (xiHeatFrequency q).re)) :=
    (summable_exp_neg_mul_re_xiHeatFrequency ha2).mul_left η
  have hle := Summable.tsum_le_tsum hpt
    (hsum.of_nonneg_of_le (fun q => by split_ifs <;> positivity) hpt) hsum
  rw [tsum_mul_left] at hle
  refine hle.trans ?_
  rw [← hS, hη, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-! ## The lower bound -/

/-- **Negative family.**  For a nonempty finite set `G` of upper off-line frequencies there are
polynomials `P_u` (`u ∈ G`) with `Re H_a(Σ x_u P_u) < 0` for every nonzero `x`. -/
theorem exists_heatHankel_negative_family {a : ℝ} (ha : 0 < a) (G : Finset ℂ) (hGne : G.Nonempty)
    (hG : ∀ u ∈ G, u ∈ xiUpperFrequencies) :
    ∃ P : G → ℂ[X], ∀ x : G → ℂ, x ≠ 0 → (heatHankel a (∑ u, x u • P u) (∑ u, x u • P u)).re < 0 := by
  classical
  have hGim : ∀ u ∈ G, 0 < u.im := fun u hu => by
    obtain ⟨q, -, h⟩ := hG u hu
    exact h
  have hqs : ∀ u : G, ∃ q : XiZeroCopy, xiHeatFrequency q = u := fun u => by
    obtain ⟨q, hq, -⟩ := hG u u.2
    exact ⟨q, hq⟩
  choose qs hqs using hqs
  set Gc := G ∪ G.image (starRingEnd ℂ) with hGc
  have hGc_conj : ∀ p ∈ Gc, (starRingEnd ℂ) p ∈ Gc := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨p, hp, rfl⟩)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hp
      rw [Complex.conj_conj]
      exact Finset.mem_union_left _ hu
  -- the separation constant
  set RG := ∑ u ∈ G, ‖u‖ with hRG
  have hRG0 : 0 ≤ RG := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hRGu : ∀ u ∈ G, ‖u‖ ≤ RG := fun u hu =>
    Finset.single_le_sum (f := fun u => ‖u‖) (fun _ _ => norm_nonneg _) hu
  obtain ⟨d, hd, hdsep⟩ := exists_pos_le_norm_sub G (heatFrequenciesBelow (2 * RG + 2))
  set C₀ := 2 + (2 * RG + 3) / d with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ (2 * RG + 3) / d := by positivity
    rw [hC₀]; linarith
  have hratio : ∀ u ∈ G, ∀ v : ℂ, (∃ q : XiZeroCopy, xiHeatFrequency q = v) → v ∉ Gc →
      ∀ w : ℂ, ‖w - v‖ ≤ C₀ * (1 + ‖w‖) * ‖u - v‖ := by
    intro u hu v hv hvG w
    refine norm_sub_le_of_far_or_sep hd (hRGu u hu) fun hvn => ?_
    obtain ⟨q, hq⟩ := hv
    refine hdsep u hu v (mem_heatFrequenciesBelow.2 ⟨q, hq, ?_⟩) ?_ ?_
    · exact (Complex.re_le_norm v).trans hvn.le
    · rintro rfl
      exact hvG (Finset.mem_union_left _ hu)
    · rintro rfl
      exact hvG (Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, hu, rfl⟩))
  -- the interpolating factors
  obtain ⟨NN, hNN⟩ : ∃ NN : G → ℂ[X],
      ∀ u : G, NN u = heatRootPoly ((Gc.erase (u : ℂ)).erase ((starRingEnd ℂ) u)) := ⟨_, fun _ => rfl⟩
  have hNu : ∀ u : G, (NN u).eval (u : ℂ) ≠ 0 := fun u => by
    rw [hNN]
    exact eval_heatRootPoly_ne_zero fun h => (Finset.mem_erase.1 (Finset.mem_erase.1 h).2).1 rfl
  have hNuc : ∀ u : G, (NN u).eval ((starRingEnd ℂ) u) ≠ 0 := fun u => by
    rw [hNN]
    exact eval_heatRootPoly_ne_zero fun h => (Finset.mem_erase.1 h).1 rfl
  have hNvan : ∀ u v : G, u ≠ v → (NN u).eval (v : ℂ) = 0 ∧ (NN u).eval ((starRingEnd ℂ) v) = 0 := by
    intro u v huv
    have hne : (v : ℂ) ≠ u := fun h => huv (Subtype.ext h).symm
    have hu := hGim u u.2
    have hv := hGim v v.2
    rw [hNN]
    constructor
    · refine eval_heatRootPoly_eq_zero (Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨hne,
        Finset.mem_union_left _ v.2⟩⟩)
      intro h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    · refine eval_heatRootPoly_eq_zero (Finset.mem_erase.2 ⟨fun h => hne ((starRingEnd ℂ).injective h),
        Finset.mem_erase.2 ⟨?_, hGc_conj _ (Finset.mem_union_left _ v.2)⟩⟩)
      intro h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
  -- uniform bounds for the interpolating factors
  obtain ⟨Bu, hBu⟩ : ∃ Bu : G → ℝ,
      ∀ u : G, Bu u = (polyMass (NN u) * (2 * (1 + ‖(u : ℂ)‖))) ^ 2 := ⟨_, fun _ => rfl⟩
  have hBu0 : ∀ u, 0 ≤ Bu u := fun u => by rw [hBu]; exact sq_nonneg _
  set Ball := ∑ u, Bu u with hBall
  set Nall := ∑ u : G, 2 * ((NN u).natDegree + 1) with hNall
  have hBall0 : 0 ≤ Ball := Finset.sum_nonneg fun u _ => hBu0 u
  have hBuall : ∀ u, Bu u ≤ Ball := fun u =>
    Finset.single_le_sum (fun u _ => hBu0 u) (Finset.mem_univ u)
  have hnuall : ∀ u : G, 2 * ((NN u).natDegree + 1) ≤ Nall := fun u =>
    Finset.single_le_sum (f := fun u : G => 2 * ((NN u).natDegree + 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
  have hLbound : ∀ u : G, ∀ w : ℂ,
      (‖(NN u).eval w‖ * (‖w - (starRingEnd ℂ) u‖ + ‖w - u‖)) ^ 2 ≤ Ball * (1 + ‖w‖) ^ Nall := by
    intro u w
    have h1 := norm_eval_le_polyMass (NN u) w
    have hm0 := polyMass_nonneg (NN u)
    have h2 : ‖w - (starRingEnd ℂ) u‖ + ‖w - u‖ ≤ 2 * (1 + ‖(u : ℂ)‖) * (1 + ‖w‖) := by
      have e1 : ‖w - (starRingEnd ℂ) u‖ ≤ ‖w‖ + ‖(u : ℂ)‖ := by
        have := norm_sub_le w ((starRingEnd ℂ) (u : ℂ))
        rwa [Complex.norm_conj] at this
      have e2 := norm_sub_le w (u : ℂ)
      nlinarith [norm_nonneg w, norm_nonneg (u : ℂ), mul_nonneg (norm_nonneg w) (norm_nonneg (u : ℂ))]
    have h3 : ‖(NN u).eval w‖ * (‖w - (starRingEnd ℂ) u‖ + ‖w - u‖) ≤
        polyMass (NN u) * (2 * (1 + ‖(u : ℂ)‖)) * (1 + ‖w‖) ^ ((NN u).natDegree + 1) := by
      calc ‖(NN u).eval w‖ * (‖w - (starRingEnd ℂ) u‖ + ‖w - u‖)
          ≤ polyMass (NN u) * (1 + ‖w‖) ^ (NN u).natDegree *
              (2 * (1 + ‖(u : ℂ)‖) * (1 + ‖w‖)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    have h4 : (1 + ‖w‖) ^ (2 * ((NN u).natDegree + 1)) ≤ (1 + ‖w‖) ^ Nall :=
      pow_le_pow_right₀ (by linarith [norm_nonneg w]) (hnuall u)
    calc (‖(NN u).eval w‖ * (‖w - (starRingEnd ℂ) u‖ + ‖w - u‖)) ^ 2
        ≤ (polyMass (NN u) * (2 * (1 + ‖(u : ℂ)‖)) * (1 + ‖w‖) ^ ((NN u).natDegree + 1)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h3 2
      _ = Bu u * (1 + ‖w‖) ^ (2 * ((NN u).natDegree + 1)) := by
          rw [hBu, mul_pow, ← pow_mul, mul_comm ((NN u).natDegree + 1) 2]
      _ ≤ Ball * (1 + ‖w‖) ^ Nall := mul_le_mul (hBuall u) h4 (by positivity) hBall0
  -- the gap constants
  obtain ⟨cu, hcu⟩ : ∃ cu : G → ℝ, ∀ u : G, cu u = Real.exp (-(a * (u : ℂ).re)) *
      (‖(NN u).eval (u : ℂ)‖ * ‖(NN u).eval ((starRingEnd ℂ) u)‖ *
        ‖(u : ℂ) - (starRingEnd ℂ) u‖ ^ 2) := ⟨_, fun _ => rfl⟩
  have hcu0 : ∀ u, 0 < cu u := fun u => by
    have hdu : (u : ℂ) - (starRingEnd ℂ) u ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith [hGim u u.2]
    have h1 := norm_pos_iff.2 (hNu u)
    have h2 := norm_pos_iff.2 (hNuc u)
    have h3 := norm_pos_iff.2 hdu
    rw [hcu]
    positivity
  obtain ⟨u₀, -, hu₀⟩ := (Finset.univ : Finset G).exists_min_image cu
    (Finset.univ_nonempty_iff.2 hGne.to_subtype)
  set cmin := cu u₀ with hcmin
  have hcmin0 : 0 < cmin := hcu0 u₀
  set m : ℝ := (G.card : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set ε := cmin / (2 * (m * Ball + 1)) with hε
  have hε0 : 0 < ε := div_pos hcmin0 (by nlinarith)
  have hεsmall : m * Ball * ε < cmin := by
    have hmB : 0 ≤ m * Ball := mul_nonneg hm0 hBall0
    rw [hε, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith [mul_nonneg hmB hcmin0.le]
  -- the level
  obtain ⟨Dc, hDc0, hDc⟩ := exists_card_heatFrequenciesBelow_le
  obtain ⟨Λ, hΛ₀, hΛ0, hsmall⟩ := exists_level_tail_small ha hC₀1 hDc0 Nall hε0 (2 * RG + 2)
  set Rset := heatFrequenciesBelow Λ \ Gc with hRset
  set k := Rset.card with hk
  have hkD : (k : ℝ) ≤ Dc * (Λ + 7) ^ (5 / 8 : ℝ) := by
    have h1 : (k : ℝ) ≤ (heatFrequenciesBelow Λ).card := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    exact h1.trans (hDc Λ hΛ0)
  have htail := hsmall k hkD
  set K := heatRootPoly Rset with hK
  have hRconj : ∀ v ∈ Rset, (starRingEnd ℂ) v ∈ Rset := by
    intro v hv
    rw [Finset.mem_sdiff] at hv ⊢
    refine ⟨conj_mem_heatFrequenciesBelow hv.1, fun h => hv.2 ?_⟩
    have := hGc_conj _ h
    rwa [Complex.conj_conj] at this
  have hKconj : ∀ w, K.eval ((starRingEnd ℂ) w) = (starRingEnd ℂ) (K.eval w) :=
    eval_heatRootPoly_conj hRconj
  have hKu : ∀ u : G, K.eval (u : ℂ) ≠ 0 := fun u =>
    eval_heatRootPoly_ne_zero fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_union_left _ u.2)
  have hKbound : ∀ u : G, ∀ w : ℂ, ‖K.eval w‖ ≤ (C₀ * (1 + ‖w‖)) ^ k * ‖K.eval (u : ℂ)‖ := by
    intro u w
    refine norm_eval_heatRootPoly_le fun v hv => ?_
    have hv' := Finset.mem_sdiff.1 hv
    obtain ⟨q, hq, -⟩ := mem_heatFrequenciesBelow.1 hv'.1
    exact hratio u u.2 v ⟨q, hq⟩ hv'.2 w
  -- the phases and the polynomials
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : G → ℂ, ∀ u : G, Ω u = Complex.exp (-(a : ℂ) * u) * K.eval (u : ℂ) *
      (starRingEnd ℂ) (K.eval ((starRingEnd ℂ) u)) *
      ((NN u).eval (u : ℂ) * (starRingEnd ℂ) ((NN u).eval ((starRingEnd ℂ) u))) *
      ((u : ℂ) - (starRingEnd ℂ) u) ^ 2 := ⟨_, fun _ => rfl⟩
  have hΩnorm : ∀ u : G, ‖Ω u‖ = cu u * ‖K.eval (u : ℂ)‖ ^ 2 := by
    intro u
    rw [hΩ, hcu, hKconj, Complex.conj_conj]
    simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_exp]
    have : (-(a : ℂ) * (u : ℂ)).re = -(a * (u : ℂ).re) := by simp
    rw [this]
    ring
  have hΩne : ∀ u, Ω u ≠ 0 := fun u => by
    rw [← norm_ne_zero_iff, hΩnorm]
    have := hcu0 u
    have := norm_pos_iff.2 (hKu u)
    positivity
  obtain ⟨t, ht⟩ : ∃ t : G → ℂ, ∀ u : G, t u = -(Ω u / (‖Ω u‖ : ℂ)) := ⟨_, fun _ => rfl⟩
  have htn : ∀ u, ‖t u‖ = 1 := fun u => by
    rw [ht, norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.2 (hΩne u))]
  obtain ⟨P, hP⟩ : ∃ P : G → ℂ[X], ∀ u : G, P u = K * (NN u *
      ((X - C ((starRingEnd ℂ) (u : ℂ))) + C (t u) * (X - C (u : ℂ)))) := ⟨_, fun _ => rfl⟩
  have hPeval : ∀ u : G, ∀ w : ℂ, (P u).eval w = K.eval w * ((NN u).eval w *
      ((w - (starRingEnd ℂ) u) + t u * (w - u))) := fun u w => by
    rw [hP]; simp
  refine ⟨P, fun x hx => ?_⟩
  -- the rank-two values
  have hval : ∀ u : G, heatHankelTermAt a (P u) (P u) u = -(((‖Ω u‖ : ℝ)) : ℂ) := by
    intro u
    have heq : heatHankelTermAt a (P u) (P u) u = Ω u * (starRingEnd ℂ) (t u) := by
      rw [heatHankelTermAt, hPeval, hPeval, hΩ]
      simp only [sub_self, mul_zero, add_zero, zero_add, map_mul, map_sub, Complex.conj_conj]
      ring
    rw [heq, ht]
    have hn : (‖Ω u‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (hΩne u)
    rw [map_neg, map_div₀, Complex.conj_ofReal, mul_neg, mul_div_assoc', Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  -- the tails
  have htailu : ∀ u : G, ∑' q : XiZeroCopy, heatHankelTail a Λ (P u) q ≤
      2 * Ball * ‖K.eval (u : ℂ)‖ ^ 2 * ε := by
    intro u
    have hpt : ∀ q : XiZeroCopy, heatHankelTail a Λ (P u) q ≤ 2 * Ball * ‖K.eval (u : ℂ)‖ ^ 2 *
        (if Λ < (xiHeatFrequency q).re then Real.exp (-(a * (xiHeatFrequency q).re)) *
          ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ Nall)
          else 0) := by
      intro q
      unfold heatHankelTail
      split_ifs with hq
      · set w := xiHeatFrequency q with hw
        have hone : ∀ z : ℂ, ‖(P u).eval z‖ ^ 2 ≤
            (C₀ * (1 + ‖z‖)) ^ (2 * k) * ‖K.eval (u : ℂ)‖ ^ 2 * (Ball * (1 + ‖z‖) ^ Nall) := by
          intro z
          rw [hPeval]
          have hL : ‖(NN u).eval z * ((z - (starRingEnd ℂ) u) + t u * (z - u))‖ ≤
              ‖(NN u).eval z‖ * (‖z - (starRingEnd ℂ) u‖ + ‖z - u‖) := by
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
            rw [norm_mul, htn, one_mul]
          have hL2 := (pow_le_pow_left₀ (norm_nonneg _) hL 2).trans (hLbound u z)
          have hK2 := pow_le_pow_left₀ (norm_nonneg _) (hKbound u z) 2
          rw [norm_mul, mul_pow]
          calc ‖K.eval z‖ ^ 2 * ‖(NN u).eval z * ((z - (starRingEnd ℂ) u) + t u * (z - u))‖ ^ 2
              ≤ ((C₀ * (1 + ‖z‖)) ^ k * ‖K.eval (u : ℂ)‖) ^ 2 * (Ball * (1 + ‖z‖) ^ Nall) :=
                mul_le_mul hK2 hL2 (by positivity) (by positivity)
            _ = (C₀ * (1 + ‖z‖)) ^ (2 * k) * ‖K.eval (u : ℂ)‖ ^ 2 * (Ball * (1 + ‖z‖) ^ Nall) := by
                rw [mul_pow, ← pow_mul, mul_comm k 2]
        have h1 := hone w
        have h2 := hone ((starRingEnd ℂ) w)
        rw [Complex.norm_conj] at h2
        have he := (Real.exp_pos (-(a * w.re))).le
        calc Real.exp (-(a * w.re)) * (‖(P u).eval w‖ ^ 2 + ‖(P u).eval ((starRingEnd ℂ) w)‖ ^ 2)
            ≤ Real.exp (-(a * w.re)) * (2 * ((C₀ * (1 + ‖w‖)) ^ (2 * k) * ‖K.eval (u : ℂ)‖ ^ 2 *
                (Ball * (1 + ‖w‖) ^ Nall))) := by
              refine mul_le_mul_of_nonneg_left ?_ he
              linarith
          _ = 2 * Ball * ‖K.eval (u : ℂ)‖ ^ 2 * (Real.exp (-(a * w.re)) *
                ((C₀ * (1 + ‖w‖)) ^ (2 * k) * (1 + ‖w‖) ^ Nall)) := by ring
      · simp
    have hsum : Summable fun q : XiZeroCopy =>
        (if Λ < (xiHeatFrequency q).re then Real.exp (-(a * (xiHeatFrequency q).re)) *
          ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ Nall)
          else 0) := by
      refine ((summable_one_add_norm_pow_mul_exp ha (2 * k + Nall)).mul_left
        (C₀ ^ (2 * k))).of_nonneg_of_le (fun q => by split_ifs <;> positivity) fun q => ?_
      split_ifs
      · rw [mul_pow, pow_add]
        have := (Real.exp_pos (-(a * (xiHeatFrequency q).re))).le
        apply le_of_eq
        ring
      · positivity
    calc ∑' q : XiZeroCopy, heatHankelTail a Λ (P u) q
        ≤ ∑' q : XiZeroCopy, 2 * Ball * ‖K.eval (u : ℂ)‖ ^ 2 *
            (if Λ < (xiHeatFrequency q).re then Real.exp (-(a * (xiHeatFrequency q).re)) *
              ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ Nall)
              else 0) :=
          Summable.tsum_le_tsum hpt (summable_heatHankelTail ha Λ (P u)) (hsum.mul_left _)
      _ = 2 * Ball * ‖K.eval (u : ℂ)‖ ^ 2 * ∑' q : XiZeroCopy,
            (if Λ < (xiHeatFrequency q).re then Real.exp (-(a * (xiHeatFrequency q).re)) *
              ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * k) * (1 + ‖xiHeatFrequency q‖) ^ Nall)
              else 0) := tsum_mul_left
      _ ≤ 2 * Ball * ‖K.eval (u : ℂ)‖ ^ 2 * ε := mul_le_mul_of_nonneg_left htail (by positivity)
  -- assembly
  have hle := re_heatHankel_sum_le ha P (fun u : G => (u : ℂ)) qs (fun u => ‖Ω u‖) (Λ := Λ)
    hqs (fun u => hGim u u.2) Subtype.val_injective
    (fun u => (Complex.re_le_norm _).trans ((hRGu u u.2).trans (by linarith)))
    (fun q hq hnot u => by
      have hmemR : xiHeatFrequency q ∈ Rset := by
        refine Finset.mem_sdiff.2 ⟨mem_heatFrequenciesBelow.2 ⟨q, rfl, hq⟩, fun h => ?_⟩
        rcases Finset.mem_union.1 h with h | h
        · exact (hnot ⟨_, h⟩).1 rfl
        · obtain ⟨v, hv, hvq⟩ := Finset.mem_image.1 h
          exact (hnot ⟨v, hv⟩).2 hvq.symm
      constructor
      · rw [hPeval, eval_heatRootPoly_eq_zero hmemR, zero_mul]
      · rw [hPeval, eval_heatRootPoly_eq_zero (hRconj _ hmemR), zero_mul])
    (fun u v huv => by
      constructor
      · rw [hPeval, (hNvan u v huv).1, zero_mul, mul_zero]
      · rw [hPeval, (hNvan u v huv).2, zero_mul, mul_zero])
    hval (fun u => norm_nonneg _) x
  rw [Fintype.card_coe] at hle
  refine hle.trans_lt ?_
  obtain ⟨u₁, hu₁⟩ : ∃ u, x u ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hbr : ∀ u : G, (G.card : ℝ) / 2 * (∑' q : XiZeroCopy, heatHankelTail a Λ (P u) q) -
      ‖Ω u‖ < 0 := by
    intro u
    have hKpos : 0 < ‖K.eval (u : ℂ)‖ ^ 2 := by have := norm_pos_iff.2 (hKu u); positivity
    have h1 : (G.card : ℝ) / 2 * (∑' q : XiZeroCopy, heatHankelTail a Λ (P u) q) ≤
        m * Ball * ε * ‖K.eval (u : ℂ)‖ ^ 2 := by
      calc (G.card : ℝ) / 2 * (∑' q : XiZeroCopy, heatHankelTail a Λ (P u) q)
          ≤ (G.card : ℝ) / 2 * (2 * Ball * ‖K.eval (u : ℂ)‖ ^ 2 * ε) :=
            mul_le_mul_of_nonneg_left (htailu u) (by positivity)
        _ = m * Ball * ε * ‖K.eval (u : ℂ)‖ ^ 2 := by rw [hm]; ring
    have h2 : cmin * ‖K.eval (u : ℂ)‖ ^ 2 ≤ ‖Ω u‖ := by
      rw [hΩnorm]
      exact mul_le_mul_of_nonneg_right (hu₀ u (Finset.mem_univ _)) (by positivity)
    have h3 : m * Ball * ε * ‖K.eval (u : ℂ)‖ ^ 2 < cmin * ‖K.eval (u : ℂ)‖ ^ 2 :=
      mul_lt_mul_of_pos_right hεsmall hKpos
    linarith
  calc ∑ u, ‖x u‖ ^ 2 * ((G.card : ℝ) / 2 * (∑' q : XiZeroCopy, heatHankelTail a Λ (P u) q) -
        ‖Ω u‖)
      < 0 := by
        refine Finset.sum_neg' (fun u _ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
          (hbr u).le) ⟨u₁, Finset.mem_univ _, mul_neg_of_pos_of_neg (by positivity) (hbr u₁)⟩

/-- **Lower bound.**  For every finite set `G` of upper off-line frequencies there is a subspace of
`ℂ[X]` of dimension `#G` on which the heat Hankel form is negative definite. -/
theorem exists_heatHankel_negative_subspace {a : ℝ} (ha : 0 < a) (G : Finset ℂ)
    (hG : ∀ u ∈ G, u ∈ xiUpperFrequencies) :
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = G.card ∧
      ∀ P ∈ V, P ≠ 0 → (heatHankel a P P).re < 0 := by
  classical
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · exact ⟨⊥, by simp [hGe], fun P hP hP0 => absurd ((Submodule.mem_bot ℂ).1 hP) hP0⟩
  obtain ⟨P, hneg⟩ := exists_heatHankel_negative_family ha G hGne hG
  set Φ : (G → ℂ) →ₗ[ℂ] ℂ[X] := Fintype.linearCombination ℂ P with hΦ
  have hΦapp : ∀ x, Φ x = ∑ u, x u • P u := fun x => Fintype.linearCombination_apply ℂ P x
  have hzero : heatHankel a 0 0 = 0 := by simp [heatHankel, heatHankelTermAt]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have := hneg x hne
    rw [← hΦapp, hx, hzero, zero_re] at this
    exact lt_irrefl 0 this
  refine ⟨LinearMap.range Φ, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  · rintro c ⟨x, rfl⟩ hc
    have hx : x ≠ 0 := by
      rintro rfl
      exact hc (map_zero Φ)
    rw [hΦapp]
    exact hneg x hx

/-- **Hermite's theorem for the zero heat trace, finite case.**  If the set `U` of upper off-line
frequencies is finite, the negative index of the heat Hankel form `H_a` is exactly `#U`, for every
`a > 0`. -/
theorem heatHankel_negativeIndex_eq_card {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite) :
    (∀ V : Submodule ℂ ℂ[X], (∀ P ∈ V, P ≠ 0 → (heatHankel a P P).re < 0) →
      Module.finrank ℂ V ≤ hU.toFinset.card) ∧
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = hU.toFinset.card ∧
      ∀ P ∈ V, P ≠ 0 → (heatHankel a P P).re < 0 :=
  ⟨fun V hV => finrank_le_of_heatHankel_neg ha hU V hV,
    exists_heatHankel_negative_subspace ha hU.toFinset fun _ hu => hU.mem_toFinset.1 hu⟩

/-- **Hermite's theorem for the zero heat trace, infinite case.**  If there are infinitely many
off-line zero quadruples, the heat Hankel form has negative definite subspaces of every dimension. -/
theorem heatHankel_negative_subspace_of_infinite {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Infinite) (n : ℕ) :
    ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = n ∧
      ∀ P ∈ V, P ≠ 0 → (heatHankel a P P).re < 0 := by
  obtain ⟨G, hGU, hGcard⟩ := hU.exists_subset_card_eq n
  obtain ⟨V, hV, hneg⟩ := exists_heatHankel_negative_subspace ha G fun u hu => hGU hu
  exact ⟨V, hV.trans hGcard, hneg⟩

/-- **RH as Hankel positivity.**  For `a > 0`, RH holds iff the heat Hankel form
`Σ_q e^{-a w_q} P(w_q) \overline{P(\overline{w_q})}` is nonnegative on every polynomial. -/
theorem riemannHypothesis_iff_heatHankel_nonneg {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ P : ℂ[X], 0 ≤ (heatHankel a P P).re := by
  refine ⟨fun hRH P => heatHankel_re_nonneg_of_riemannHypothesis ha hRH P, fun h => ?_⟩
  by_contra hRH
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero] at hRH
  push Not at hRH
  obtain ⟨q, hq⟩ := hRH
  have hw := (xiHeatFrequency_im_ne_zero_iff q).2 hq
  obtain ⟨u, hu⟩ : ∃ u, u ∈ xiUpperFrequencies := by
    rcases lt_or_gt_of_ne hw with h | h
    · refine ⟨_, xiZeroCopyLineConjEquiv q, rfl, ?_⟩
      rw [xiHeatFrequency_lineConj, Complex.conj_im]
      linarith
    · exact ⟨_, q, rfl, h⟩
  obtain ⟨V, hV, hneg⟩ := exists_heatHankel_negative_subspace ha {u} (by simpa using hu)
  rw [Finset.card_singleton] at hV
  have hVbot : V ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hV
    exact zero_ne_one hV
  obtain ⟨P, hPV, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVbot
  exact absurd (h P) (not_le.2 (hneg P hPV hP0))

end

end RHTower
