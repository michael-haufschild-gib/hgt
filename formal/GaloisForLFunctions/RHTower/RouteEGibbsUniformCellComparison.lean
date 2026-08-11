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

end RouteEPhysicalFibreData

end

end RHTower
