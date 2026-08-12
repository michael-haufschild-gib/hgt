import GaloisForLFunctions.RHTower.RouteEUniformComparisonEndpoint

/-!
# Route E Gibbs-to-uniform comparison on finite cells

Pairwise logarithmic oscillation of a positive weight controls the difference between its
normalized weighted mean and the uniform mean.  This closes the finite measure-change step from
all-order product-history Gibbs stability to the replica-orbit endpoint.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

section FiniteLikelihoodRatio

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Pairwise multiplicative oscillation gives a uniform pointwise bound on normalized weights. -/
theorem routeE_normalizedWeight_sub_uniform_abs_le
    (weight : Ω → ℝ) (E : ℝ)
    (hweight : ∀ x, 0 < weight x) (hE : 1 ≤ E)
    (hratio : ∀ x y, weight x ≤ E * weight y) (x : Ω) :
    |weight x / (∑ y, weight y) - 1 / (Fintype.card Ω : ℝ)| ≤
      (E - 1) / (Fintype.card Ω : ℝ) := by
  let W := ∑ y, weight y
  let N : ℝ := Fintype.card Ω
  have hW : 0 < W := Finset.sum_pos (fun y _hy => hweight y) (Finset.univ_nonempty)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hupperSum : N * weight x ≤ E * W := by
    dsimp [N, W]
    calc
      (Fintype.card Ω : ℝ) * weight x = ∑ _y : Ω, weight x := by simp
      _ ≤ ∑ y : Ω, E * weight y :=
        Finset.sum_le_sum fun y _hy => hratio x y
      _ = E * ∑ y : Ω, weight y := by rw [Finset.mul_sum]
  have hlowerSum : W ≤ N * E * weight x := by
    dsimp [N, W]
    calc
      (∑ y : Ω, weight y) ≤ ∑ _y : Ω, E * weight x :=
        Finset.sum_le_sum fun y _hy => hratio y x
      _ = (Fintype.card Ω : ℝ) * (E * weight x) := by simp
      _ = (Fintype.card Ω : ℝ) * E * weight x := by ring
  have hupper : weight x / W ≤ E / N := by
    apply (div_le_div_iff₀ hW hN).2
    nlinarith
  have hlower : 1 / (N * E) ≤ weight x / W := by
    apply (div_le_div_iff₀ (mul_pos hN hEpos) hW).2
    nlinarith
  rw [abs_le]
  constructor
  · have hrecip : (E - 1) / (N * E) ≤ (E - 1) / N := by
      apply div_le_div_of_nonneg_left (sub_nonneg.mpr hE) hN
      simpa using mul_le_mul_of_nonneg_left hE hN.le
    have hid : 1 / N - 1 / (N * E) = (E - 1) / (N * E) := by
      field_simp [ne_of_gt hN, ne_of_gt hEpos]
    have : 1 / N - weight x / W ≤ (E - 1) / N := by
      calc
        1 / N - weight x / W ≤ 1 / N - 1 / (N * E) := sub_le_sub_left hlower _
        _ = (E - 1) / (N * E) := hid
        _ ≤ (E - 1) / N := hrecip
    linarith
  · have hid : E / N - 1 / N = (E - 1) / N := by ring
    calc
      weight x / W - 1 / N ≤ E / N - 1 / N := sub_le_sub_right hupper _
      _ = (E - 1) / N := hid

/-- Uniform comparison for every observable bounded by one. -/
theorem routeE_abs_weightedMean_sub_uniformMean_le_ratioDefect
    (weight observable : Ω → ℝ) (E : ℝ)
    (hweight : ∀ x, 0 < weight x) (hE : 1 ≤ E)
    (hratio : ∀ x y, weight x ≤ E * weight y)
    (hobservable : ∀ x, |observable x| ≤ 1) :
    |(∑ x, weight x * observable x) / (∑ x, weight x) -
        (∑ x, observable x) / (Fintype.card Ω : ℝ)| ≤ E - 1 := by
  let W := ∑ x, weight x
  let N : ℝ := Fintype.card Ω
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hpoint : ∀ x,
      |weight x / W - 1 / N| ≤ (E - 1) / N := by
    intro x
    exact routeE_normalizedWeight_sub_uniform_abs_le weight E hweight hE hratio x
  have hidentity :
      (∑ x, weight x * observable x) / W - (∑ x, observable x) / N =
        ∑ x, (weight x / W - 1 / N) * observable x := by
    rw [Finset.sum_div, Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hidentity]
  calc
    |∑ x, (weight x / W - 1 / N) * observable x| ≤
        ∑ x, |(weight x / W - 1 / N) * observable x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Ω, (E - 1) / N := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [abs_mul]
      calc
        |weight x / W - 1 / N| * |observable x| ≤
            ((E - 1) / N) * 1 :=
          mul_le_mul (hpoint x) (hobservable x) (abs_nonneg _) (by
            exact div_nonneg (sub_nonneg.mpr hE) hN.le)
        _ = (E - 1) / N := by ring
    _ = E - 1 := by
      simp [N]
      field_simp [ne_of_gt hN]

omit [Fintype Ω] [Nonempty Ω] in
/-- An absolute logarithmic ratio bound exponentiates to pairwise multiplicative oscillation. -/
theorem routeE_weight_ratio_le_exp_of_abs_log_ratio
    (weight : Ω → ℝ) (eta : ℝ)
    (hweight : ∀ x, 0 < weight x)
    (hlog : ∀ x y, |Real.log (weight x / weight y)| ≤ eta) (x y : Ω) :
    weight x ≤ Real.exp eta * weight y := by
  have hratioPos : 0 < weight x / weight y := div_pos (hweight x) (hweight y)
  have hlogUpper : Real.log (weight x / weight y) ≤ eta :=
    (le_abs_self _).trans (hlog x y)
  have hexp := Real.exp_le_exp.mpr hlogUpper
  rw [Real.exp_log hratioPos] at hexp
  exact (div_le_iff₀ (hweight y)).mp hexp

/-- Pairwise ratio oscillation by a square factor gives a square-root finite mean defect.
The square-root dependence is stronger than the direct `E - 1` estimate and remains bounded by
two even for large likelihood-ratio oscillation. -/
theorem routeE_abs_weightedMean_sub_uniformMean_le_sqrtRatioDefect
    (weight observable : Ω → ℝ) (s : ℝ)
    (hweight : ∀ x, 0 < weight x) (hs : 1 ≤ s)
    (hratio : ∀ x y, weight x ≤ s ^ 2 * weight y)
    (hobservable : ∀ x, |observable x| ≤ 1) :
    |(∑ x, weight x * observable x) / (∑ x, weight x) -
        (∑ x, observable x) / (Fintype.card Ω : ℝ)| ≤
      2 * (s - 1) / (s + 1) := by
  classical
  rcases hs.eq_or_lt with rfl | hslt
  · simpa using routeE_abs_weightedMean_sub_uniformMean_le_ratioDefect
      weight observable 1 hweight le_rfl (by simpa using hratio) hobservable
  let values : Finset ℝ := Finset.univ.image weight
  have hvalues : values.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let L : ℝ := values.min' hvalues
  have hLmem : L ∈ values := Finset.min'_mem values hvalues
  obtain ⟨x₀, _hx₀, hx₀⟩ := Finset.mem_image.mp hLmem
  have hLvalue : weight x₀ = L := hx₀
  have hLpos : 0 < L := by
    rw [← hLvalue]
    exact hweight x₀
  have hLle : ∀ x, L ≤ weight x := by
    intro x
    exact Finset.min'_le values (weight x)
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  let U : ℝ := s ^ 2 * L
  have hweightU : ∀ x, weight x ≤ U := by
    intro x
    dsimp [U]
    simpa [hLvalue] using hratio x x₀
  let N : ℝ := Fintype.card Ω
  let W : ℝ := ∑ x, weight x
  let a : ℝ := W / N
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hW : 0 < W := by
    dsimp [W]
    exact Finset.sum_pos (fun x _hx => hweight x) Finset.univ_nonempty
  have hWa : W = N * a := by
    dsimp [a]
    field_simp [ne_of_gt hN]
  have haPos : 0 < a := by
    rw [hWa] at hW
    exact pos_of_mul_pos_right hW hN.le
  have hLa : L ≤ a := by
    have hsum : N * L ≤ W := by
      dsimp [N, W]
      calc
        (Fintype.card Ω : ℝ) * L = ∑ _x : Ω, L := by simp
        _ ≤ ∑ x : Ω, weight x := Finset.sum_le_sum fun x _hx => hLle x
    rw [hWa] at hsum
    exact le_of_mul_le_mul_left hsum hN
  have haU : a ≤ U := by
    have hsum : W ≤ N * U := by
      dsimp [N, W]
      calc
        (∑ x : Ω, weight x) ≤ ∑ _x : Ω, U :=
          Finset.sum_le_sum fun x _hx => hweightU x
        _ = (Fintype.card Ω : ℝ) * U := by simp
    rw [hWa] at hsum
    exact le_of_mul_le_mul_left hsum hN
  have hUL : 0 < U - L := by
    dsimp [U]
    have hsSq : 1 < s ^ 2 := by nlinarith
    nlinarith
  let kappa : ℝ := (U - a) / (U - L)
  have hkappa : 0 ≤ kappa := div_nonneg (sub_nonneg.mpr haU) hUL.le
  have hpositivePart : ∀ x,
      max (weight x - a) 0 ≤ kappa * (weight x - L) := by
    intro x
    rcases le_total (weight x) a with hxa | hax
    · rw [max_eq_right (sub_nonpos.mpr hxa)]
      exact mul_nonneg hkappa (sub_nonneg.mpr (hLle x))
    · rw [max_eq_left (sub_nonneg.mpr hax)]
      dsimp [kappa]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hUL).2
      have hcore : (weight x - a) * (U - L) ≤ (U - a) * (weight x - L) := by
        nlinarith [hLle x, hweightU x]
      simpa [mul_assoc] using hcore
  have hdevsum : (∑ x, (weight x - a)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change W - N * a = 0
    rw [← hWa]
    ring
  have habsPoint : ∀ x,
      |weight x - a| = 2 * max (weight x - a) 0 - (weight x - a) := by
    intro x
    rcases le_total (weight x) a with hxa | hax
    · rw [abs_of_nonpos (sub_nonpos.mpr hxa), max_eq_right (sub_nonpos.mpr hxa)]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr hax), max_eq_left (sub_nonneg.mpr hax)]
      ring
  have habssumEq : (∑ x, |weight x - a|) =
      2 * ∑ x, max (weight x - a) 0 := by
    simp_rw [habsPoint]
    rw [Finset.sum_sub_distrib, Finset.mul_sum, hdevsum, sub_zero]
  have hpositiveSum : (∑ x, max (weight x - a) 0) ≤
      kappa * N * (a - L) := by
    calc
      (∑ x, max (weight x - a) 0) ≤ ∑ x, kappa * (weight x - L) :=
        Finset.sum_le_sum fun x _hx => hpositivePart x
      _ = kappa * ∑ x, (weight x - L) := by rw [Finset.mul_sum]
      _ = kappa * N * (a - L) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change kappa * (W - N * L) = kappa * N * (a - L)
        rw [hWa]
        ring
  have habssum : (∑ x, |weight x - a|) ≤
      2 * kappa * N * (a - L) := by
    rw [habssumEq]
    nlinarith
  have hmeanIdentity :
      (∑ x, weight x * observable x) / W - (∑ x, observable x) / N =
        (∑ x, (weight x - a) * observable x) / W := by
    rw [Finset.sum_div, Finset.sum_div]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [hWa]
    field_simp [ne_of_gt hN, ne_of_gt haPos]
  have hmeanAbs :
      |(∑ x, weight x * observable x) / W - (∑ x, observable x) / N| ≤
        (∑ x, |weight x - a|) / W := by
    rw [hmeanIdentity, abs_div, abs_of_pos hW]
    apply div_le_div_of_nonneg_right _ hW.le
    calc
      |∑ x, (weight x - a) * observable x| ≤
          ∑ x, |(weight x - a) * observable x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |weight x - a| := by
        apply Finset.sum_le_sum
        intro x _hx
        rw [abs_mul]
        simpa using mul_le_of_le_one_right (abs_nonneg (weight x - a)) (hobservable x)
  have hcore : (U - a) * (a - L) ≤ a * L * (s - 1) ^ 2 := by
    have hid : a * L * (s - 1) ^ 2 - (U - a) * (a - L) =
        (a - s * L) ^ 2 := by
      dsimp [U]
      ring
    nlinarith [sq_nonneg (a - s * L)]
  have hsharpCore : (U - a) * (a - L) / (a * (U - L)) ≤
      (s - 1) / (s + 1) := by
    apply (div_le_div_iff₀ (mul_pos haPos hUL) (by positivity : 0 < s + 1)).2
    calc
      (U - a) * (a - L) * (s + 1) ≤
          (a * L * (s - 1) ^ 2) * (s + 1) :=
        mul_le_mul_of_nonneg_right hcore (by positivity)
      _ = (s - 1) * (a * (U - L)) := by
        dsimp [U]
        ring
  change |(∑ x, weight x * observable x) / W - (∑ x, observable x) / N| ≤ _
  calc
    |(∑ x, weight x * observable x) / W - (∑ x, observable x) / N| ≤
        (∑ x, |weight x - a|) / W := hmeanAbs
    _ ≤ (2 * kappa * N * (a - L)) / W :=
      div_le_div_of_nonneg_right habssum hW.le
    _ = 2 * ((U - a) * (a - L) / (a * (U - L))) := by
      dsimp [kappa]
      rw [hWa]
      field_simp [ne_of_gt hN, ne_of_gt haPos, ne_of_gt hUL]
    _ ≤ 2 * ((s - 1) / (s + 1)) :=
      mul_le_mul_of_nonneg_left hsharpCore (by norm_num)
    _ = 2 * (s - 1) / (s + 1) := by ring

/-- Exponential square-root ratio defect in hyperbolic form. -/
theorem routeE_two_expHalfRatio_eq_two_tanh_quarter (eta : ℝ) :
    2 * (Real.exp (eta / 2) - 1) / (Real.exp (eta / 2) + 1) =
      2 * Real.tanh (eta / 4) := by
  rw [Real.tanh_eq]
  have hhalf : Real.exp (eta / 2) =
      Real.exp (eta / 4) * Real.exp (eta / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hhalf, Real.exp_neg]
  field_simp [Real.exp_ne_zero (eta / 4)]

/-- The sharp likelihood-ratio defect is nonnegative for nonnegative log oscillation. -/
theorem routeE_two_tanh_quarter_nonneg {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ 2 * Real.tanh (eta / 4) := by
  rw [← routeE_two_expHalfRatio_eq_two_tanh_quarter eta]
  exact div_nonneg
    (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp (by positivity))))
    (le_of_lt (by positivity : 0 < Real.exp (eta / 2) + 1))

/-- Pairwise logarithmic likelihood-ratio oscillation gives the square-root
physical-versus-uniform mean defect `2 tanh (eta / 4)`. -/
theorem routeE_abs_weightedMean_sub_uniformMean_le_tanhDefect
    (weight observable : Ω → ℝ) (eta : ℝ)
    (hweight : ∀ x, 0 < weight x) (heta : 0 ≤ eta)
    (hlog : ∀ x y, |Real.log (weight x / weight y)| ≤ eta)
    (hobservable : ∀ x, |observable x| ≤ 1) :
    |(∑ x, weight x * observable x) / (∑ x, weight x) -
        (∑ x, observable x) / (Fintype.card Ω : ℝ)| ≤
      2 * Real.tanh (eta / 4) := by
  have hs : 1 ≤ Real.exp (eta / 2) := Real.one_le_exp (by positivity)
  have hsq : Real.exp (eta / 2) ^ 2 = Real.exp eta := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h := routeE_abs_weightedMean_sub_uniformMean_le_sqrtRatioDefect
    weight observable (Real.exp (eta / 2)) hweight hs
    (fun x y => by
      rw [hsq]
      exact routeE_weight_ratio_le_exp_of_abs_log_ratio weight eta hweight hlog x y)
    hobservable
  rw [routeE_two_expHalfRatio_eq_two_tanh_quarter] at h
  exact h

/-- Logarithmic Gibbs oscillation gives the explicit finite-cell comparison defect `exp eta - 1`. -/
theorem routeE_abs_weightedMean_sub_uniformMean_le_expDefect
    (weight observable : Ω → ℝ) (eta : ℝ)
    (hweight : ∀ x, 0 < weight x) (heta : 0 ≤ eta)
    (hlog : ∀ x y, |Real.log (weight x / weight y)| ≤ eta)
    (hobservable : ∀ x, |observable x| ≤ 1) :
    |(∑ x, weight x * observable x) / (∑ x, weight x) -
        (∑ x, observable x) / (Fintype.card Ω : ℝ)| ≤ Real.exp eta - 1 := by
  apply routeE_abs_weightedMean_sub_uniformMean_le_ratioDefect
    weight observable (Real.exp eta) hweight
  · exact Real.one_le_exp heta
  · intro x y
    exact routeE_weight_ratio_le_exp_of_abs_log_ratio weight eta hweight hlog x y
  · exact hobservable

end FiniteLikelihoodRatio

section ProductHistoryCell

variable {Ω R : Type*} [Fintype Ω] [Nonempty Ω] [Fintype R]

/-- **All-order product-history physical/uniform comparison.**  On any finite product cell inside
one common aperture, equal products make the normalized product-Gibbs character mean differ from
the uniform character mean by at most the explicit exponential curvature defect. -/
theorem routeE_productHistoryGibbsMean_sub_uniformMean_le
    (X H : ℝ) (history : Ω → R → ℝ) (observable : Ω → ℝ)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ ω r, history ω r ∈ Set.Icc (X - H) (X + H))
    (hproduct : ∀ ω ξ, ∏ r, history ω r = ∏ r, history ξ r)
    (hobservable : ∀ ω, |observable ω| ≤ 1) :
    |(∑ ω, routeEProductHistoryGibbsWeight X (history ω) * observable ω) /
          (∑ ω, routeEProductHistoryGibbsWeight X (history ω)) -
        (∑ ω, observable ω) / (Fintype.card Ω : ℝ)| ≤
      Real.exp ((Fintype.card R : ℝ) * H ^ 2 / (X * (X - H))) - 1 := by
  let eta := (Fintype.card R : ℝ) * H ^ 2 / (X * (X - H))
  have hXH : 0 < X - H := sub_pos.mpr hHX
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  apply routeE_abs_weightedMean_sub_uniformMean_le_expDefect
    (fun ω => routeEProductHistoryGibbsWeight X (history ω)) observable eta
  · intro ω
    rw [routeEProductHistoryGibbsWeight_eq_exp_sum]
    exact Real.exp_pos _
  · exact heta
  · intro ω ξ
    exact routeEProductHistory_abs_log_gibbs_ratio_le X H
      (history ω) (history ξ) hX hH hHX (haperture ω) (haperture ξ) (hproduct ω ξ)
  · exact hobservable

/-- **All-order product-history square-root likelihood endpoint.** Equal products in one common
aperture give the stronger hyperbolic physical-versus-uniform defect. -/
theorem routeE_productHistoryGibbsMean_sub_uniformMean_le_tanh
    (X H : ℝ) (history : Ω → R → ℝ) (observable : Ω → ℝ)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ ω r, history ω r ∈ Set.Icc (X - H) (X + H))
    (hproduct : ∀ ω ξ, ∏ r, history ω r = ∏ r, history ξ r)
    (hobservable : ∀ ω, |observable ω| ≤ 1) :
    |(∑ ω, routeEProductHistoryGibbsWeight X (history ω) * observable ω) /
          (∑ ω, routeEProductHistoryGibbsWeight X (history ω)) -
        (∑ ω, observable ω) / (Fintype.card Ω : ℝ)| ≤
      2 * Real.tanh
        (((Fintype.card R : ℝ) * H ^ 2 / (X * (X - H))) / 4) := by
  let eta := (Fintype.card R : ℝ) * H ^ 2 / (X * (X - H))
  have hXH : 0 < X - H := sub_pos.mpr hHX
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  apply routeE_abs_weightedMean_sub_uniformMean_le_tanhDefect
    (fun ω => routeEProductHistoryGibbsWeight X (history ω)) observable eta
  · intro ω
    rw [routeEProductHistoryGibbsWeight_eq_exp_sum]
    exact Real.exp_pos _
  · exact heta
  · intro ω ξ
    exact routeEProductHistory_abs_log_gibbs_ratio_le X H
      (history ω) (history ξ) hX hH hHX (haperture ω) (haperture ξ) (hproduct ω ξ)
  · exact hobservable

end ProductHistoryCell

namespace RouteEPhysicalFibreData

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Λ]

/-- Uniform counting mean on a declared physical fibre. -/
def uniformFibreMean (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) : ℝ :=
  (∑ ω with D.label ω = l, D.observable ω) /
    ((Finset.univ.filter fun ω => D.label ω = l).card : ℝ)

theorem fibreCard_pos (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) :
    0 < (Finset.univ.filter fun ω => D.label ω = l).card := by
  obtain ⟨ω, hω⟩ := D.label_surjective l
  exact Finset.card_pos.mpr ⟨ω, by simp [hω]⟩

/-- Pairwise log-density oscillation inside every fibre gives a literal comparison between the
physical conditional mean and its uniform counting mean. -/
theorem abs_conditionalMean_sub_uniformFibreMean_le_expDefect
    (D : RouteEPhysicalFibreData Ω Λ) (eta : Λ → ℝ)
    (heta : ∀ l, 0 ≤ eta l)
    (hlog : ∀ l ω ξ, D.label ω = l → D.label ξ = l →
      |Real.log (D.mass ω / D.mass ξ)| ≤ eta l)
    (hobservable : ∀ ω, |D.observable ω| ≤ 1) (l : Λ) :
    |D.conditionalMean l - D.uniformFibreMean l| ≤ Real.exp (eta l) - 1 := by
  classical
  let fibre := {ω : Ω // D.label ω = l}
  let witness : fibre :=
    ⟨Classical.choose (D.label_surjective l), Classical.choose_spec (D.label_surjective l)⟩
  letI : Nonempty fibre := ⟨witness⟩
  have hcompare := routeE_abs_weightedMean_sub_uniformMean_le_expDefect
    (Ω := fibre) (fun z => D.mass z.1) (fun z => D.observable z.1) (eta l)
    (fun z => D.mass_pos z.1) (heta l)
    (fun z w => hlog l z.1 w.1 z.2 w.2) (fun z => hobservable z.1)
  have hmass : (∑ z : fibre, D.mass z.1) = D.fibreMass l := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun ω => D.label ω = l) (by simp) D.mass]
    rfl
  have hmoment : (∑ z : fibre, D.mass z.1 * D.observable z.1) = D.fibreMoment l := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun ω => D.label ω = l) (by simp)
      (fun ω => D.mass ω * D.observable ω)]
    rfl
  have huniformSum : (∑ z : fibre, D.observable z.1) =
      ∑ ω with D.label ω = l, D.observable ω := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun ω => D.label ω = l) (by simp)
      D.observable]
  have hcard : Fintype.card fibre =
      (Finset.univ.filter fun ω => D.label ω = l).card := by
    exact Fintype.card_subtype (fun ω => D.label ω = l)
  rw [hmass, hmoment, huniformSum, hcard] at hcompare
  exact hcompare

/-- Pairwise fibrewise log-density oscillation gives the stronger square-root likelihood defect
between the physical conditional mean and uniform counting mean. -/
theorem abs_conditionalMean_sub_uniformFibreMean_le_tanhDefect
    (D : RouteEPhysicalFibreData Ω Λ) (eta : Λ → ℝ)
    (heta : ∀ l, 0 ≤ eta l)
    (hlog : ∀ l ω ξ, D.label ω = l → D.label ξ = l →
      |Real.log (D.mass ω / D.mass ξ)| ≤ eta l)
    (hobservable : ∀ ω, |D.observable ω| ≤ 1) (l : Λ) :
    |D.conditionalMean l - D.uniformFibreMean l| ≤
      2 * Real.tanh (eta l / 4) := by
  classical
  let fibre := {ω : Ω // D.label ω = l}
  let witness : fibre :=
    ⟨Classical.choose (D.label_surjective l), Classical.choose_spec (D.label_surjective l)⟩
  letI : Nonempty fibre := ⟨witness⟩
  have hcompare := routeE_abs_weightedMean_sub_uniformMean_le_tanhDefect
    (Ω := fibre) (fun z => D.mass z.1) (fun z => D.observable z.1) (eta l)
    (fun z => D.mass_pos z.1) (heta l)
    (fun z w => hlog l z.1 w.1 z.2 w.2) (fun z => hobservable z.1)
  have hmass : (∑ z : fibre, D.mass z.1) = D.fibreMass l := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun ω => D.label ω = l) (by simp) D.mass]
    rfl
  have hmoment : (∑ z : fibre, D.mass z.1 * D.observable z.1) = D.fibreMoment l := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun ω => D.label ω = l) (by simp)
      (fun ω => D.mass ω * D.observable ω)]
    rfl
  have huniformSum : (∑ z : fibre, D.observable z.1) =
      ∑ ω with D.label ω = l, D.observable ω := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun ω => D.label ω = l) (by simp)
      D.observable]
  have hcard : Fintype.card fibre =
      (Finset.univ.filter fun ω => D.label ω = l).card := by
    exact Fintype.card_subtype (fun ω => D.label ω = l)
  rw [hmass, hmoment, huniformSum, hcard] at hcompare
  exact hcompare

/-- Uniform reference energy plus the explicit fibrewise likelihood-ratio defect controls the
original physical signed mean. -/
theorem abs_mean_le_uniformReferenceEnergy_add_expDefect
    (D : RouteEPhysicalFibreData Ω Λ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hcompare : ∀ l,
      |D.conditionalMean l - D.uniformFibreMean l| ≤ delta) :
    |∑ ω, D.mass ω * D.observable ω| ≤
      Real.sqrt (2 * D.referenceFibreEnergy D.uniformFibreMean + 2 * delta ^ 2) :=
  D.abs_mean_le_sqrt_two_reference_add_two_defect_sq
    D.uniformFibreMean delta hdelta hcompare

/-- **Uniform-orbit physical endpoint.**  A common logarithmic Gibbs oscillation bound on every
fibre automatically supplies the comparison premise and yields the exact `exp eta - 1` endpoint. -/
theorem abs_mean_le_uniformReferenceEnergy_of_logOscillation
    (D : RouteEPhysicalFibreData Ω Λ) (eta : ℝ) (heta : 0 ≤ eta)
    (hlog : ∀ l ω ξ, D.label ω = l → D.label ξ = l →
      |Real.log (D.mass ω / D.mass ξ)| ≤ eta)
    (hobservable : ∀ ω, |D.observable ω| ≤ 1) :
    |∑ ω, D.mass ω * D.observable ω| ≤
      Real.sqrt (2 * D.referenceFibreEnergy D.uniformFibreMean +
        2 * (Real.exp eta - 1) ^ 2) := by
  apply D.abs_mean_le_uniformReferenceEnergy_add_expDefect (Real.exp eta - 1)
  · exact sub_nonneg.mpr (Real.one_le_exp heta)
  · intro l
    exact D.abs_conditionalMean_sub_uniformFibreMean_le_expDefect
      (fun _ => eta) (fun _ => heta) (fun l ω ξ hω hξ => hlog l ω ξ hω hξ)
        hobservable l

/-- **Square-root uniform-orbit physical endpoint.** The pairwise likelihood-ratio input enters only
through the square-root defect `2 tanh (eta / 4)`. -/
theorem abs_mean_le_uniformReferenceEnergy_of_logOscillation_tanh
    (D : RouteEPhysicalFibreData Ω Λ) (eta : ℝ) (heta : 0 ≤ eta)
    (hlog : ∀ l ω ξ, D.label ω = l → D.label ξ = l →
      |Real.log (D.mass ω / D.mass ξ)| ≤ eta)
    (hobservable : ∀ ω, |D.observable ω| ≤ 1) :
    |∑ ω, D.mass ω * D.observable ω| ≤
      Real.sqrt (2 * D.referenceFibreEnergy D.uniformFibreMean +
        2 * (2 * Real.tanh (eta / 4)) ^ 2) := by
  apply D.abs_mean_le_uniformReferenceEnergy_add_expDefect (2 * Real.tanh (eta / 4))
  · exact routeE_two_tanh_quarter_nonneg heta
  · intro l
    exact D.abs_conditionalMean_sub_uniformFibreMean_le_tanhDefect
      (fun _ => eta) (fun _ => heta) (fun l ω ξ hω hξ => hlog l ω ξ hω hξ)
        hobservable l

end RouteEPhysicalFibreData

end

end RHTower
