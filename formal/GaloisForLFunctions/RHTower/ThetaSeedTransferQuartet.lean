import GaloisForLFunctions.RHTower.ThetaSeedHalfLineDivision
import GaloisForLFunctions.RHTower.ThetaEndpointPositiveDeformation

/-!
# Positive seed transfer of an off-line quartet

Let `α` be a first-quadrant zero of `F = XiC` of multiplicity `m`, `L = [α^m, ᾱ^m]` and
`P_α(z) = ∏_{β ∈ L} (1 − z²/β²)`.  The real partial-fraction combination of the successive zero
divisions of `k` realizing `z² F / P_α` gives a real even `C^∞` source `u_α`, `|u_α| ≤ Ck`, of zero
mass with `u_α / k → 0`; the same combination applied to the seed `h` gives a real seed `v_α`,
`|v_α| ≤ Ch` on `x ≥ 0`, `v_α / h → 0`, and by commutation of zero division with the Euler resolvent
`u_α(x) = Σ n^{-1/2} v_α(x + log n)` on `x ≥ 0`.

For small `ε > 0`, `k + εu_α > 0` on `ℝ`, `h + εv_α > 0` on `x ≥ 0`, the Euler identity holds for the
perturbed pair, the perturbed source has the mass, the leading theta tail and exactly the real
divisor of `F`, its transform is `F (P_α + εz²) / P_α`: the quartet `{±α, ±ᾱ}` is removed, every other
zero of `F` remains, and the new non-real zeros are the roots of `P_α + εz²`, a polynomial of the
degree of `P_α` without real roots whose roots stay near the quartet for small `ε`.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Linear structure of seed-dominated functions -/

theorem SeedDominated.const_mul_sub {f g : ℝ → ℂ} (hf : SeedDominated f) (hg : SeedDominated g)
    (a b : ℂ) : SeedDominated fun x => a * f x - b * g x := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.exists_bound_nonneg
  obtain ⟨Cg, hCg0, hCg⟩ := hg.exists_bound_nonneg
  refine ⟨(hf.stronglyMeasurable.const_mul a).sub (hg.stronglyMeasurable.const_mul b),
    ‖a‖ * Cf + ‖b‖ * Cg, fun y hy => ?_⟩
  calc ‖a * f y - b * g y‖ ≤ ‖a‖ * ‖f y‖ + ‖b‖ * ‖g y‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * (Cf * thetaCuspLogSeed y) + ‖b‖ * (Cg * thetaCuspLogSeed y) := by
        gcongr
        · exact hCf y hy
        · exact hCg y hy
    _ = _ := by ring

theorem SeedDominated.const_mul {f : ℝ → ℂ} (hf : SeedDominated f) (a : ℂ) :
    SeedDominated fun x => a * f x := by
  have h := hf.const_mul_sub hf a 0
  simp only [zero_mul, sub_zero] at h
  exact h

theorem seedResolvent_const_mul_sub {f g : ℝ → ℂ} (hf : SeedDominated f) (hg : SeedDominated g)
    (a b : ℂ) (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) :
    seedResolvent S (fun y => a * f y - b * g y) x =
      a * seedResolvent S f x - b * seedResolvent S g x := by
  unfold seedResolvent
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub
    ((hf.summable_seedResolvent S hx).mul_left a) ((hg.summable_seedResolvent S hx).mul_left b)]
  exact tsum_congr fun n => by ring

theorem seedResolvent_const_mul {f : ℝ → ℂ} (hf : SeedDominated f) (a : ℂ) (S : Set ℕ) {x : ℝ}
    (hx : 0 ≤ x) : seedResolvent S (fun y => a * f y) x = a * seedResolvent S f x := by
  have h := seedResolvent_const_mul_sub hf hf a 0 S hx
  simp only [zero_mul, sub_zero] at h
  exact h

/-! ## The seed partial-fraction combination -/

theorem seedDominated_listComb (L : List ℂ) (e : Polynomial ℂ) :
    SeedDominated (listComb seedListDivision L e) := by
  induction L generalizing e with
  | nil => exact (seedDominated_seedListDivision []).const_mul _
  | cons β L ih => exact (seedDominated_seedListDivision (β :: L)).const_mul_sub (ih _) _ _

/-- **Seed transfer of partial fractions.**  `R (listComb (T_· h) L e) = listComb G_· L e` on the
physical half-line. -/
theorem seedResolvent_listComb (L : List ℂ) (e : Polynomial ℂ) {x : ℝ} (hx : 0 ≤ x) :
    seedResolvent univ (listComb seedListDivision L e) x = listComb thetaListDivision L e x := by
  induction L generalizing e with
  | nil =>
    rw [listComb_nil, listComb_nil, seedResolvent_const_mul (seedDominated_seedListDivision []) _ _
      hx, seedResolvent_seedListDivision [] hx]
  | cons β L ih =>
    rw [listComb_cons, listComb_cons, seedResolvent_const_mul_sub
      (seedDominated_seedListDivision (β :: L)) (seedDominated_listComb L _) _ _ _ hx,
      seedResolvent_seedListDivision (β :: L) hx, ih]

/-- **Seed tail of partial fractions.**  `v − e_{|L|} ∏(−β²) h = o(h)` at `+∞`. -/
theorem tendsto_listComb_seed_sub_div (L : List ℂ) (e : Polynomial ℂ)
    (he : e.natDegree ≤ L.length) :
    Tendsto (fun x => ‖listComb seedListDivision L e x -
      e.coeff L.length * (L.map fun β => -β ^ 2).prod * thetaSeedC x‖ / thetaCuspLogSeed x)
      atTop (𝓝 0) := by
  induction L generalizing e with
  | nil =>
    simp only [listComb_nil, seedListDivision, halfListDivision, List.length_nil, List.map_nil,
      List.prod_nil, mul_one, sub_self, norm_zero, zero_div]
    exact tendsto_const_nhds
  | cons β L ih =>
    rw [listComb_cons]
    set a := β ^ 2
    set e₁ := e /ₘ (Polynomial.X - Polynomial.C a)
    have he₁ : e₁.natDegree ≤ L.length := natDegree_divByMonic_X_sub_C_le (by simpa using he) a
    have hcoeff : e.coeff (L.length + 1) = e₁.coeff L.length :=
      coeff_succ_eq_coeff_divByMonic (by simpa using he) a
    set c' := e₁.coeff L.length * (L.map fun β => -β ^ 2).prod
    have hrew : ∀ x, e.eval a * seedListDivision (β :: L) x -
        a * listComb seedListDivision L e₁ x -
        e.coeff (β :: L).length * ((β :: L).map fun β => -β ^ 2).prod * thetaSeedC x =
        e.eval a * seedListDivision (β :: L) x -
          a * (listComb seedListDivision L e₁ x - c' * thetaSeedC x) := by
      intro x
      simp only [List.length_cons, List.map_cons, List.prod_cons, hcoeff, c', a]
      ring
    simp_rw [hrew]
    have hlim : Tendsto (fun x => ‖e.eval a‖ * (‖seedListDivision (β :: L) x‖ / thetaCuspLogSeed x) +
        ‖a‖ * (‖listComb seedListDivision L e₁ x - c' * thetaSeedC x‖ / thetaCuspLogSeed x))
        atTop (𝓝 0) := by
      simpa using (((seedListDivision_tail β L).2).const_mul ‖e.eval a‖).add
        ((ih e₁ he₁).const_mul ‖a‖)
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact div_nonneg (norm_nonneg _) (thetaCuspLogSeed_pos hx).le
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have hh := thetaCuspLogSeed_pos hx
      rw [div_le_iff₀ hh]
      calc ‖e.eval a * seedListDivision (β :: L) x -
            a * (listComb seedListDivision L e₁ x - c' * thetaSeedC x)‖
          ≤ ‖e.eval a‖ * ‖seedListDivision (β :: L) x‖ +
            ‖a‖ * ‖listComb seedListDivision L e₁ x - c' * thetaSeedC x‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
        _ = _ := by field_simp

/-- Admissible partial-fraction combinations are `C^∞`. -/
theorem contDiff_listComb {L : List ℂ} (hL : ThetaDivisionList L) (e : Polynomial ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (listComb thetaListDivision L e) := by
  induction L generalizing e with
  | nil => exact contDiff_const.mul (contDiff_thetaListDivision hL)
  | cons β L ih =>
    exact (contDiff_const.mul (contDiff_thetaListDivision hL)).sub
      (contDiff_const.mul (ih hL.tail _))

/-! ## Partial-fraction sources of a finite selection of quartets -/

theorem conj_eval_map_ofReal (N : Polynomial ℝ) (w : ℂ) :
    (starRingEnd ℂ) ((N.map (algebraMap ℝ ℂ)).eval w) =
      (N.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) w) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun r => Complex.conj_ofReal r

section Selection

variable {l : List ℂ}

/-- The real source `u_N` with `Fourier(u_N) = F N(z²) / P_L`, `L = quadrantListOf l`, realized by
the real partial-fraction combination of successive zero divisions of `k`. -/
def rationalSource (l : List ℂ) (N : Polynomial ℝ) (x : ℝ) : ℝ :=
  (listComb thetaListDivision (quadrantListOf l) (N.map (algebraMap ℝ ℂ)) x).re

/-- The real physical-half-line seed `v_N`: the same combination applied to `h`. -/
def rationalSeed (l : List ℂ) (N : Polynomial ℝ) (x : ℝ) : ℝ :=
  (listComb seedListDivision (quadrantListOf l) (N.map (algebraMap ℝ ℂ)) x).re

/-- **The partial-fraction source.**  `u_N` is real, even, `C^∞`, bounded by `Ck`, with
`û_N P_L = F N(z²)`, `u_N − N_{|L|} r k = o(k)` (`r = ∏(−β²)`), and mass `N(0) ∫ k`. -/
theorem rationalSource_spec (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (hnd : l.Nodup)
    (N : Polynomial ℝ) (hN : N.natDegree ≤ (quadrantListOf l).length) {r : ℝ}
    (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (rationalSource l N) ∧
      (∀ x, rationalSource l N (-x) = rationalSource l N x) ∧
      (∃ C, ∀ x, |rationalSource l N x| ≤ C * thetaCuspFullSource x) ∧
      (∀ z, sourceTransform (fun x => (rationalSource l N x : ℂ)) z *
        listDivisor (quadrantListOf l) z = XiC z * (N.map (algebraMap ℝ ℂ)).eval (z ^ 2)) ∧
      Tendsto (fun x => |rationalSource l N x - N.coeff (quadrantListOf l).length * r *
        thetaCuspFullSource x| / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) ∧
      ∫ x, rationalSource l N x = N.eval 0 * ∫ x, thetaCuspFullSource x := by
  have hL := thetaDivisionList_quadrantListOf hl hnd
  obtain ⟨hum, hue, ⟨C, hC⟩, huT, hut⟩ :=
    listComb_spec hL (N.map (algebraMap ℝ ℂ)) (Polynomial.natDegree_map_le.trans hN)
  have hT : ∀ z, sourceTransform (fun x => (rationalSource l N x : ℂ)) z *
      listDivisor (quadrantListOf l) z = XiC z * (N.map (algebraMap ℝ ℂ)).eval (z ^ 2) := by
    intro z
    simp only [rationalSource]
    rw [sourceTransform_ofReal_re hum hue]
    have h1 := huT z
    have h2 := congrArg (starRingEnd ℂ) (huT ((starRingEnd ℂ) z))
    rw [map_mul, map_mul, XiC_conj, Complex.conj_conj, listDivisor_quadrantListOf_conj,
      conj_eval_map_ofReal, map_pow, Complex.conj_conj] at h2
    rw [div_mul_eq_mul_div, add_mul, h1, h2]
    ring
  refine ⟨Complex.reCLM.contDiff.comp (contDiff_listComb hL _), fun x => by
    simp only [rationalSource, hue], ⟨C, fun x => (Complex.abs_re_le_norm _).trans (hC x)⟩, hT,
    ?_, ?_⟩
  · refine squeeze_zero (fun x => div_nonneg (abs_nonneg _) (thetaCuspFullSource_pos x).le)
      (fun x => ?_) hut
    refine div_le_div_of_nonneg_right ?_ (thetaCuspFullSource_pos x).le
    rw [Polynomial.coeff_map, hr]
    have hre : rationalSource l N x - N.coeff (quadrantListOf l).length * r *
        thetaCuspFullSource x = (listComb thetaListDivision (quadrantListOf l)
          (N.map (algebraMap ℝ ℂ)) x - (algebraMap ℝ ℂ) (N.coeff (quadrantListOf l).length) *
            (r : ℂ) * thetaSourceC x).re := by
      simp [rationalSource, thetaSourceC]
    rw [hre]
    exact Complex.abs_re_le_norm _
  · have h0 := hT 0
    rw [listDivisor_zero, mul_one, sourceTransform_zero_ofReal, XiC_zero_eq_integral,
      zero_pow two_ne_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
      Complex.coe_algebraMap, ← Complex.ofReal_mul] at h0
    rw [← Polynomial.coeff_zero_eq_eval_zero, mul_comm]
    exact_mod_cast h0

/-- **The partial-fraction seed.**  `v_N` is bounded by `Ch` on the physical half-line,
`v_N − N_{|L|} r h = o(h)` at `+∞`, and `u_N(x) = Σ_{n ≥ 1} n^{-1/2} v_N(x + log n)` for `x ≥ 0`. -/
theorem rationalSeed_spec (N : Polynomial ℝ) (hN : N.natDegree ≤ (quadrantListOf l).length)
    {r : ℝ} (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ)) :
    (∃ C, ∀ x, 0 ≤ x → |rationalSeed l N x| ≤ C * thetaCuspLogSeed x) ∧
      Tendsto (fun x => |rationalSeed l N x - N.coeff (quadrantListOf l).length * r *
        thetaCuspLogSeed x| / thetaCuspLogSeed x) atTop (𝓝 0) ∧
      ∀ x, 0 ≤ x → rationalSource l N x =
        ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) * rationalSeed l N (x + Real.log n) := by
  have hv := seedDominated_listComb (quadrantListOf l) (N.map (algebraMap ℝ ℂ))
  obtain ⟨C, hC0, hC⟩ := hv.exists_bound_nonneg
  refine ⟨⟨C, fun x hx => (Complex.abs_re_le_norm _).trans (hC x hx)⟩, ?_, fun x hx => ?_⟩
  · have ht := tendsto_listComb_seed_sub_div (quadrantListOf l) (N.map (algebraMap ℝ ℂ))
      (Polynomial.natDegree_map_le.trans hN)
    rw [Polynomial.coeff_map, hr] at ht
    refine squeeze_zero' ?_ ?_ ht
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact div_nonneg (abs_nonneg _) (thetaCuspLogSeed_pos hx).le
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have hh := thetaCuspLogSeed_pos hx
      refine div_le_div_of_nonneg_right ?_ hh.le
      have hre : rationalSeed l N x - N.coeff (quadrantListOf l).length * r *
          thetaCuspLogSeed x = (listComb seedListDivision (quadrantListOf l)
            (N.map (algebraMap ℝ ℂ)) x - (algebraMap ℝ ℂ) (N.coeff (quadrantListOf l).length) *
              (r : ℂ) * thetaSeedC x).re := by
        simp [rationalSeed, thetaSeedC]
      rw [hre]
      exact Complex.abs_re_le_norm _
  · have h1 := seedResolvent_listComb (quadrantListOf l) (N.map (algebraMap ℝ ℂ)) hx
    have h2 := seedResolvent_re hv univ hx
    rw [h1] at h2
    have h3 : ((rationalSource l N x : ℝ) : ℂ) =
        seedResolvent univ (fun y => ((rationalSeed l N y : ℝ) : ℂ)) x := h2.symm
    have h4 : ∑' n : ℕ, (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((rationalSeed l N (x + Real.log n) : ℝ) : ℂ) =
        ((∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) * rationalSeed l N (x + Real.log n) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun n => (Complex.ofReal_mul _ _).symm
    rw [seedResolvent, tsum_univ (f := fun n : ℕ => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((rationalSeed l N (x + Real.log n) : ℝ) : ℂ)), h4] at h3
    exact_mod_cast h3

end Selection

/-! ## A single off-line quartet -/

section Quartet

variable {α : ℂ}

/-- The off-line quartet `{α, ᾱ, −α, −ᾱ}`. -/
def xiQuartetSet (α : ℂ) : Set ℂ := {α, (starRingEnd ℂ) α, -α, -(starRingEnd ℂ) α}

/-- The real even source `u_α` with `Fourier(u_α) = z² F / P_α`. -/
def quartetSource (α : ℂ) : ℝ → ℝ := rationalSource [α] Polynomial.X

/-- The real physical-half-line seed `v_α`, the same partial-fraction combination applied to `h`. -/
def quartetSeed (α : ℂ) : ℝ → ℝ := rationalSeed [α] Polynomial.X

theorem mem_singleton_quadrant (hα : α ∈ xiQuadrantZeros) :
    ∀ a ∈ [α], a ∈ xiQuadrantZeros := fun a ha => by
  rw [List.mem_singleton] at ha; exact ha ▸ hα

theorem two_le_length_quadrantListOf_singleton (hα : α ∈ xiQuadrantZeros) :
    2 ≤ (quadrantListOf [α]).length := by
  rw [length_quadrantListOf]
  have := one_le_xiZeroMult hα.2.2
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  omega

/-- **The quartet source.**  `u_α` is real, even, `C^∞`, bounded by `Ck`, of zero mass, with
`û_α P_α = F z²` and `u_α / k → 0` at both ends. -/
theorem quartetSource_spec (hα : α ∈ xiQuadrantZeros) :
    ContDiff ℝ (⊤ : ℕ∞) (quartetSource α) ∧ (∀ x, quartetSource α (-x) = quartetSource α x) ∧
      (∃ C, ∀ x, |quartetSource α x| ≤ C * thetaCuspFullSource x) ∧
      (∀ z, sourceTransform (fun x => (quartetSource α x : ℂ)) z *
        listDivisor (quadrantListOf [α]) z = XiC z * z ^ 2) ∧
      Tendsto (fun x => quartetSource α x / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) ∧
      ∫ x, quartetSource α x = 0 := by
  unfold quartetSource
  have hl := mem_singleton_quadrant hα
  have hlen := two_le_length_quadrantListOf_singleton hα
  obtain ⟨r, -, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨hc, he, hC, hT, ht, hm⟩ := rationalSource_spec hl (List.nodup_singleton α)
    Polynomial.X (Polynomial.natDegree_X_le.trans (by omega)) hr
  have hcoeff : (Polynomial.X : Polynomial ℝ).coeff (quadrantListOf [α]).length = 0 :=
    Polynomial.coeff_X_of_ne_one (by omega)
  refine ⟨hc, he, hC, fun z => ?_, ?_, ?_⟩
  · rw [hT z, Polynomial.map_X, Polynomial.eval_X]
  · rw [hcoeff] at ht
    refine tendsto_iff_norm_sub_tendsto_zero.2 (ht.congr fun x => ?_)
    rw [zero_mul, zero_mul, sub_zero, sub_zero, Real.norm_eq_abs, abs_div,
      abs_of_pos (thetaCuspFullSource_pos x)]
  · rw [hm, Polynomial.eval_X, zero_mul]

/-- **The quartet seed.**  `v_α` is bounded by `Ch` and `v_α / h → 0` on the physical half-line, and
`u_α(x) = Σ_{n ≥ 1} n^{-1/2} v_α(x + log n)` for `x ≥ 0`. -/
theorem quartetSeed_spec (hα : α ∈ xiQuadrantZeros) :
    (∃ C, ∀ x, 0 ≤ x → |quartetSeed α x| ≤ C * thetaCuspLogSeed x) ∧
      Tendsto (fun x => quartetSeed α x / thetaCuspLogSeed x) atTop (𝓝 0) ∧
      ∀ x, 0 ≤ x → quartetSource α x =
        ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) * quartetSeed α (x + Real.log n) := by
  unfold quartetSeed quartetSource
  have hl := mem_singleton_quadrant hα
  have hlen := two_le_length_quadrantListOf_singleton hα
  obtain ⟨r, -, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨hC, ht, hE⟩ := rationalSeed_spec (l := [α]) Polynomial.X
    (Polynomial.natDegree_X_le.trans (by omega)) hr
  have hcoeff : (Polynomial.X : Polynomial ℝ).coeff (quadrantListOf [α]).length = 0 :=
    Polynomial.coeff_X_of_ne_one (by omega)
  refine ⟨hC, ?_, hE⟩
  rw [hcoeff] at ht
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' ?_ ?_ ht)
  · exact Eventually.of_forall fun x => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hh := thetaCuspLogSeed_pos hx
    rw [zero_mul, zero_mul, sub_zero, sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hh]

end Quartet

/-! ## The quartet divisor -/

theorem ne_zero_of_mul_eq_listDivisor {G Q : ℂ → ℂ} (hGd : Differentiable ℂ G)
    (hQd : Differentiable ℂ Q) {L : List ℂ} (h : ∀ z, G z * listDivisor L z = XiC z * Q z)
    {β : ℂ} (hle : analyticOrderAt XiC β ≤ analyticOrderAt (listDivisor L) β) (hQ : Q β ≠ 0) :
    G β ≠ 0 := by
  have hPd := differentiable_listDivisor L
  have h1 := congrArg (fun f => analyticOrderAt f β)
    (show G * listDivisor L = XiC * Q from funext h)
  rw [analyticOrderAt_mul (hGd.analyticAt β) (hPd.analyticAt β),
    analyticOrderAt_mul (XiC_differentiable.analyticAt β) (hQd.analyticAt β),
    (hQd.analyticAt β).analyticOrderAt_eq_zero.2 hQ, add_zero] at h1
  have hF := analyticOrderAt_XiC_ne_top_of_entire β
  have hP : analyticOrderAt (listDivisor L) β ≠ ⊤ := fun hP => hF (by rw [← h1, hP, add_top])
  have h2 : analyticOrderAt G β + analyticOrderAt (listDivisor L) β ≤
      0 + analyticOrderAt (listDivisor L) β := by
    rw [zero_add, h1]; exact hle
  exact (hGd.analyticAt β).analyticOrderAt_eq_zero.1
    (nonpos_iff_eq_zero.1 ((WithTop.add_le_add_iff_right hP).1 h2))

section QuartetDivisor

variable {α : ℂ}

theorem ne_zero_of_mem_xiQuadrantZeros (hα : α ∈ xiQuadrantZeros) : α ≠ 0 := fun h => by
  rw [h] at hα; simp [xiQuadrantZeros] at hα

theorem mem_quadrantListOf_singleton_iff (hα : α ∈ xiQuadrantZeros) {β : ℂ} :
    β ∈ quadrantListOf [α] ↔ β = α ∨ β = (starRingEnd ℂ) α := by
  have hm := one_le_xiZeroMult hα.2.2
  simp only [quadrantListOf, List.mem_append, List.mem_replicate, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨by omega, h⟩
    · exact Or.inr ⟨by omega, h⟩

/-- The zeros of `P_α` are exactly the quartet `{±α, ±ᾱ}`. -/
theorem listDivisor_quadrantListOf_singleton_eq_zero_iff (hα : α ∈ xiQuadrantZeros) (z : ℂ) :
    listDivisor (quadrantListOf [α]) z = 0 ↔ z ∈ xiQuartetSet α := by
  have hα0 := ne_zero_of_mem_xiQuadrantZeros hα
  have hc0 : (starRingEnd ℂ) α ≠ 0 := by simpa using hα0
  constructor
  · intro h
    obtain ⟨β, hβ, h' | h'⟩ := exists_mem_of_listDivisor_eq_zero h <;>
      rcases (mem_quadrantListOf_singleton_iff hα).1 hβ with rfl | rfl <;>
      simp [xiQuartetSet, h']
  · intro hz
    refine List.prod_eq_zero (List.mem_map.2 ?_)
    simp only [xiQuartetSet, mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨z, (mem_quadrantListOf_singleton_iff hα).2 (Or.inl rfl), by field_simp; ring⟩
    · exact ⟨_, (mem_quadrantListOf_singleton_iff hα).2 (Or.inr rfl), by field_simp; ring⟩
    · exact ⟨α, (mem_quadrantListOf_singleton_iff hα).2 (Or.inl rfl), by field_simp; ring⟩
    · exact ⟨_, (mem_quadrantListOf_singleton_iff hα).2 (Or.inr rfl), by field_simp; ring⟩

/-- `P_α` carries every quartet zero of `F` with at least its multiplicity. -/
theorem analyticOrderAt_XiC_le_quartet (hα : α ∈ xiQuadrantZeros) {β : ℂ}
    (hβ : β ∈ xiQuartetSet α) :
    analyticOrderAt XiC β ≤ analyticOrderAt (listDivisor (quadrantListOf [α])) β := by
  have hl := mem_singleton_quadrant hα
  have hPd := differentiable_listDivisor (quadrantListOf [α])
  have key : ∀ w, w = α ∨ w = (starRingEnd ℂ) α →
      analyticOrderAt XiC w ≤ analyticOrderAt (listDivisor (quadrantListOf [α])) w := by
    intro w hw
    have hre : 0 < w.re := by rcases hw with rfl | rfl <;> simpa using hα.1
    rw [analyticOrderAt_listDivisor hre _ (fun b hb => re_pos_of_mem_quadrantListOf hl hb),
      count_quadrantListOf hl (List.nodup_singleton α), if_pos, ← xiZeroMult_eq]
    rcases hw with rfl | rfl
    · exact Or.inl (List.mem_singleton_self _)
    · right; rw [Complex.conj_conj]; exact List.mem_singleton_self _
  have hneg : ∀ w, analyticOrderAt XiC (-w) ≤ analyticOrderAt (listDivisor (quadrantListOf [α])) (-w) ↔
      analyticOrderAt XiC w ≤ analyticOrderAt (listDivisor (quadrantListOf [α])) w := fun w => by
    rw [analyticOrderAt_XiC_neg_eq, analyticOrderAt_neg_of_even hPd (listDivisor_neg _)]
  simp only [xiQuartetSet, mem_insert_iff, mem_singleton_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl
  · exact key _ (Or.inl rfl)
  · exact key _ (Or.inr rfl)
  · exact (hneg _).2 (key _ (Or.inl rfl))
  · exact (hneg _).2 (key _ (Or.inr rfl))

end QuartetDivisor

/-! ## The seed-transfer deformation -/

/-- **Positive seed transfer of a partial-fraction direction.**  For every real `N` of degree
`≤ |L|` and small `ε > 0`: `k + εu_N > 0` on `ℝ`, `h + εv_N > 0` on `x ≥ 0`,
`k + εu_N = Σ n^{-1/2} (h + εv_N)(· + log n)` on `x ≥ 0`, the perturbed transform is
`F (P_L + ε N(z²)) / P_L` with exactly the real zeros of `F`, and every even moment of `u_N` that
vanishes is a moment of `k` left unchanged. -/
theorem rational_seed_transfer {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (hnd : l.Nodup)
    (N : Polynomial ℝ) (hN : N.natDegree ≤ (quadrantListOf l).length) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ x, 0 < thetaCuspFullSource x + ε * rationalSource l N x) ∧
      (∀ x, 0 ≤ x → 0 < thetaCuspLogSeed x + ε * rationalSeed l N x) ∧
      (∀ x, 0 ≤ x → thetaCuspFullSource x + ε * rationalSource l N x =
        ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (thetaCuspLogSeed (x + Real.log n) + ε * rationalSeed l N (x + Real.log n))) ∧
      (∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
        ((thetaCuspFullSource x + ε * rationalSource l N x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ) ∧
      (∀ z, sourceTransform (fun x => ((thetaCuspFullSource x + ε * rationalSource l N x : ℝ) : ℂ)) z *
        listDivisor (quadrantListOf l) z = XiC z * (listDivisor (quadrantListOf l) z +
          ε * (N.map (algebraMap ℝ ℂ)).eval (z ^ 2))) ∧
      ∀ i : ℕ, ∫ x, x ^ (2 * i) * rationalSource l N x = 0 →
        ∫ x, x ^ (2 * i) * (thetaCuspFullSource x + ε * rationalSource l N x) =
          ∫ x, x ^ (2 * i) * thetaCuspFullSource x := by
  obtain ⟨r, -, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨huc, -, ⟨Cu, huC⟩, huT, -, -⟩ := rationalSource_spec hl hnd N hN hr
  obtain ⟨⟨Cv, hCv⟩, -, hEuler⟩ := rationalSeed_spec (l := l) N hN hr
  obtain ⟨ε₁, hε₁, hdef⟩ := positive_deformation_of_mul_eq hl huc.continuous huC hN huT
  refine ⟨min ε₁ (1 / (|Cv| + 1)), lt_min hε₁ (by positivity), fun ε hε hεlt => ?_⟩
  have hε1 : ε < ε₁ := hεlt.trans_le (min_le_left _ _)
  have hε2 : ε * (|Cv| + 1) < 1 := by
    have := hεlt.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  obtain ⟨hpos, hid, -, hord⟩ := hdef ε (by rwa [abs_of_pos hε])
  refine ⟨hpos, fun x hx => ?_, fun x hx => ?_, hord, hid, fun i hi =>
    integral_pow_mul_add_smul huc.continuous huC ε hi⟩
  · -- positivity of the seed
    have hh := thetaCuspLogSeed_pos hx
    have h1 : |ε * rationalSeed l N x| ≤ ε * (|Cv| * thetaCuspLogSeed x) := by
      rw [abs_mul, abs_of_pos hε]
      exact mul_le_mul_of_nonneg_left ((hCv x hx).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) hh.le)) hε.le
    have h2 := neg_abs_le (ε * rationalSeed l N x)
    have h3 : 0 < thetaCuspLogSeed x * (1 - ε * |Cv|) := mul_pos hh (by nlinarith [abs_nonneg Cv])
    nlinarith
  · -- the Euler identity
    have hk : thetaCuspFullSource x =
        ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspLogSeed (x + Real.log n) :=
      tsum_congr fun n => (rpow_neg_half_mul_thetaCuspLogSeed n x).symm
    have hsk : Summable fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspLogSeed (x + Real.log n) :=
      (summable_thetaCuspSourceTerm x).congr fun n => (rpow_neg_half_mul_thetaCuspLogSeed n x).symm
    have hsv : Summable fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ)) * rationalSeed l N (x + Real.log n) := by
      refine ((summable_thetaCuspSourceTerm x).mul_left (max Cv 0)).of_norm_bounded fun n => ?_
      have h := norm_seedWeight_mul_le (g := fun y => ((rationalSeed l N y : ℝ) : ℂ))
        (C := max Cv 0) (fun y hy => by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (hCv y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (thetaCuspLogSeed_pos hy).le)) hx n
      rwa [← Complex.ofReal_mul, Complex.norm_real] at h
    rw [hk, hEuler x hx, ← tsum_mul_left, ← hsk.tsum_add (hsv.mul_left ε)]
    exact tsum_congr fun n => by ring

/-- **Positive seed transfer of an off-line quartet.**  If `α` is a first-quadrant zero of `F`, then
for every small `ε > 0`: `k + εu_α > 0` on `ℝ` and `h + εv_α > 0` on `x ≥ 0`, with
`k + εu_α = Σ n^{-1/2} (h + εv_α)(· + log n)` on `x ≥ 0`; the perturbed source has the same mass,
the same leading theta tail and exactly the real-zero divisor of `F`; its transform is
`F (P_α + εz²) / P_α`, the quartet `{±α, ±ᾱ}` is no longer a zero, every other zero of `F` remains,
and off the quartet its zeros are those of `F` together with those of `P_α + εz²`. -/
theorem quartet_seed_transfer (hα : α ∈ xiQuadrantZeros) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ x, 0 < thetaCuspFullSource x + ε * quartetSource α x) ∧
      (∀ x, 0 ≤ x → 0 < thetaCuspLogSeed x + ε * quartetSeed α x) ∧
      (∀ x, 0 ≤ x → thetaCuspFullSource x + ε * quartetSource α x =
        ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (thetaCuspLogSeed (x + Real.log n) + ε * quartetSeed α (x + Real.log n))) ∧
      ∫ x, (thetaCuspFullSource x + ε * quartetSource α x) = ∫ x, thetaCuspFullSource x ∧
      Tendsto (fun x => (thetaCuspFullSource x + ε * quartetSource α x) / thetaCuspFullSource x)
        (cocompact ℝ) (𝓝 1) ∧
      (∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
        ((thetaCuspFullSource x + ε * quartetSource α x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ) ∧
      (∀ z, sourceTransform (fun x => ((thetaCuspFullSource x + ε * quartetSource α x : ℝ) : ℂ)) z *
        listDivisor (quadrantListOf [α]) z =
          XiC z * (listDivisor (quadrantListOf [α]) z + ε * z ^ 2)) ∧
      (∀ β ∈ xiQuartetSet α, sourceTransform (fun x =>
        ((thetaCuspFullSource x + ε * quartetSource α x : ℝ) : ℂ)) β ≠ 0) ∧
      (∀ z ∉ xiQuartetSet α, analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform fun x =>
        ((thetaCuspFullSource x + ε * quartetSource α x : ℝ) : ℂ)) z) ∧
      ∀ z ∉ xiQuartetSet α, (sourceTransform (fun x =>
        ((thetaCuspFullSource x + ε * quartetSource α x : ℝ) : ℂ)) z = 0 ↔
          XiC z = 0 ∨ listDivisor (quadrantListOf [α]) z + ε * z ^ 2 = 0) := by
  have hl := mem_singleton_quadrant hα
  obtain ⟨huc, hue, ⟨Cu, huC⟩, huT, hut, hmass⟩ := quartetSource_spec hα
  have hlen := two_le_length_quadrantListOf_singleton hα
  obtain ⟨ε₀, hε₀, hgen⟩ := rational_seed_transfer hl (List.nodup_singleton α) Polynomial.X
    (Polynomial.natDegree_X_le.trans (by omega))
  refine ⟨ε₀, hε₀, fun ε hε hεlt => ?_⟩
  obtain ⟨hpos, hseed, hE, hord, hid, hmom⟩ := hgen ε hε hεlt
  set G := sourceTransform fun x => ((thetaCuspFullSource x + ε * quartetSource α x : ℝ) : ℂ)
  set P := listDivisor (quadrantListOf [α])
  have hid' : ∀ z, G z * P z = XiC z * (P z + ε * z ^ 2) := fun z => by
    have := hid z
    rwa [Polynomial.map_X, Polynomial.eval_X] at this
  have hGd : Differentiable ℂ G := (expMomentSource_ofReal_of_le
    (u := fun x => thetaCuspFullSource x + ε * quartetSource α x)
    (contDiff_thetaCuspFullSource.continuous.add (continuous_const.mul huc.continuous))
    (C := 1 + ε * |Cu|) (fun x => by
      have hk := thetaCuspFullSource_pos x
      have h1 : |ε * quartetSource α x| ≤ ε * (|Cu| * thetaCuspFullSource x) := by
        rw [abs_mul, abs_of_pos hε]
        exact mul_le_mul_of_nonneg_left ((huC x).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) hk.le)) hε.le
      calc |thetaCuspFullSource x + ε * quartetSource α x| ≤
            |thetaCuspFullSource x| + |ε * quartetSource α x| := abs_add_le _ _
        _ ≤ thetaCuspFullSource x + ε * (|Cu| * thetaCuspFullSource x) := by
            rw [abs_of_pos hk]; linarith
        _ = (1 + ε * |Cu|) * thetaCuspFullSource x := by ring)).differentiable_sourceTransform
  have hPd : Differentiable ℂ P := differentiable_listDivisor _
  have hQd : Differentiable ℂ fun z => P z + ε * z ^ 2 := hPd.add (by fun_prop)
  have hPz : ∀ z ∉ xiQuartetSet α, P z ≠ 0 := fun z hz h =>
    hz ((listDivisor_quadrantListOf_singleton_eq_zero_iff hα z).1 h)
  refine ⟨hpos, hseed, hE, ?_, ?_, hord, hid', fun β hβ => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · -- the mass
    have := hmom 0 (by simpa [quartetSource] using hmass)
    simpa [quartetSource] using this
  · -- the leading tail
    have := (hut.const_mul ε).const_add 1
    rw [mul_zero, add_zero] at this
    refine this.congr fun x => ?_
    have hk := (thetaCuspFullSource_pos x).ne'
    field_simp
  · -- the quartet is removed
    have hβ0 : β ≠ 0 := by
      have hα0 := ne_zero_of_mem_xiQuadrantZeros hα
      simp only [xiQuartetSet, mem_insert_iff, mem_singleton_iff] at hβ
      rcases hβ with rfl | rfl | rfl | rfl <;> simpa using hα0
    refine ne_zero_of_mul_eq_listDivisor hGd hQd hid' (analyticOrderAt_XiC_le_quartet hα hβ) ?_
    have hPβ : P β = 0 := (listDivisor_quadrantListOf_singleton_eq_zero_iff hα β).2 hβ
    rw [hPβ, zero_add]
    exact mul_ne_zero (by exact_mod_cast hε.ne') (pow_ne_zero 2 hβ0)
  · -- every other zero remains
    have h1 := congrArg (fun f => analyticOrderAt f z) (show G * P = XiC * fun z => P z + ε * z ^ 2
      from funext hid')
    rw [analyticOrderAt_mul (hGd.analyticAt z) (hPd.analyticAt z),
      analyticOrderAt_mul (XiC_differentiable.analyticAt z) (hQd.analyticAt z),
      (hPd.analyticAt z).analyticOrderAt_eq_zero.2 (hPz z hz), add_zero] at h1
    rw [h1]
    exact le_self_add
  · -- the zeros off the quartet
    have hP := hPz z hz
    constructor
    · intro h0
      have := hid' z
      rw [h0, zero_mul] at this
      exact mul_eq_zero.1 this.symm
    · intro h0
      have := hid' z
      rw [mul_eq_zero.2 h0] at this
      exact (mul_eq_zero.1 this).resolve_right hP

/-- **The replacing roots.**  `P_α + εz²` has the degree `2|L| = 4m` of `P_α`, no real root for
`ε > 0`, and for small `ε` all its roots lie in prescribed neighbourhoods of the quartet. -/
theorem quartet_perturbed_divisor (hα : α ∈ xiQuadrantZeros) :
    (∀ ε : ℂ, ∃ Q : Polynomial ℂ, Q.natDegree = 2 * (quadrantListOf [α]).length ∧
      ∀ z, Q.eval z = listDivisor (quadrantListOf [α]) z + ε * z ^ 2) ∧
    (∀ ε : ℝ, 0 < ε → ∀ x : ℝ, listDivisor (quadrantListOf [α]) x + ε * (x : ℂ) ^ 2 ≠ 0) ∧
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ z : ℂ,
      listDivisor (quadrantListOf [α]) z + ε * z ^ 2 = 0 → ∃ β ∈ xiQuartetSet α, ‖z - β‖ < δ := by
  have hl := mem_singleton_quadrant hα
  have hlen := two_le_length_quadrantListOf_singleton hα
  set L := quadrantListOf [α]
  set P := listDivisor L
  have hL0 : ∀ β ∈ L, β ≠ 0 := fun β hβ h0 => by
    have := re_pos_of_mem_quadrantListOf hl hβ; rw [h0] at this; simp at this
  refine ⟨fun ε => ?_, fun ε hε x h0 => ?_, fun δ hδ => ?_⟩
  · obtain ⟨Q, -, hQd, hQe⟩ := exists_polynomial_listDivisor L hL0
    refine ⟨Q + Polynomial.C ε * Polynomial.X ^ 2, ?_, fun z => by
      rw [Polynomial.eval_add, hQe, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]⟩
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt, hQd]
    rw [hQd]
    exact (Polynomial.natDegree_C_mul_X_pow_le ε 2).trans_lt (by omega)
  · obtain ⟨r, hr, hrx⟩ := listDivisor_quadrantListOf_ofReal hl x
    replace hrx : P x = r := hrx
    rw [hrx] at h0
    have : ((r + ε * x ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have hpos : 0 < r + ε * x ^ 2 := by positivity
    exact hpos.ne' (by exact_mod_cast this)
  · -- growth at infinity
    have hc := tendsto_listDivisor_div_pow L
    obtain ⟨r, hr, hrL⟩ := prod_neg_sq_quadrantListOf hl
    have hc0 : ((L.map fun β : ℂ => -β ^ 2).prod)⁻¹ ≠ 0 := by
      rw [hrL]; exact inv_ne_zero (by exact_mod_cast hr.ne')
    set c := ((L.map fun β : ℂ => -β ^ 2).prod)⁻¹
    have hev : ∀ᶠ z in cocompact ℂ, ‖c‖ / 2 ≤ ‖P z / z ^ (2 * L.length)‖ := by
      have := hc.norm.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.2 hc0)))
      exact this.mono fun z hz => hz.le
    obtain ⟨K₀, hK₀, hK₀s⟩ := mem_cocompact.1 hev
    obtain ⟨R₀, hR₀K⟩ := hK₀.isBounded.subset_closedBall 0
    have hR₀ : ∀ z : ℂ, R₀ < dist z 0 → ‖c‖ / 2 ≤ ‖P z / z ^ (2 * L.length)‖ := fun z hz =>
      hK₀s fun hzK => absurd (Metric.mem_closedBall.1 (hR₀K hzK)) (not_le.2 hz)
    set R := max (max (R₀ + 1) 1) (2 / ‖c‖ + 1)
    have hR1 : 1 ≤ R := (le_max_right _ _).trans (le_max_left _ _)
    have hbig : ∀ z : ℂ, R ≤ ‖z‖ → ‖z‖ ^ 2 < ‖P z‖ := by
      intro z hz
      have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
      have h1 := hR₀ z (by rw [dist_zero_right]; exact lt_of_lt_of_le (by
        linarith [le_max_left (R₀ + 1) 1, le_max_left (max (R₀ + 1) 1) (2 / ‖c‖ + 1)] : R₀ < R) hz)
      rw [norm_div, norm_pow, le_div_iff₀ (pow_pos (norm_pos_iff.2 hz0) _)] at h1
      have hcR : 2 < ‖c‖ * ‖z‖ := by
        have : 2 / ‖c‖ + 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
        have hcn := norm_pos_iff.2 hc0
        rw [div_add_one hcn.ne', div_le_iff₀ hcn] at this
        nlinarith
      have hpow : ‖z‖ ^ 2 * ‖z‖ ≤ ‖z‖ ^ (2 * L.length) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ (hR1.trans hz) (by omega)
      have hz2 := pow_pos (norm_pos_iff.2 hz0) 2
      have h2 : ‖c‖ / 2 * (‖z‖ ^ 2 * ‖z‖) ≤ ‖c‖ / 2 * ‖z‖ ^ (2 * L.length) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have h3 := mul_lt_mul_of_pos_left (show 1 < ‖c‖ * ‖z‖ / 2 by linarith) hz2
      nlinarith
    -- compact region away from the quartet
    set K := Metric.closedBall (0 : ℂ) R \ ⋃ β ∈ xiQuartetSet α, Metric.ball β δ
    have hK : IsCompact K := (isCompact_closedBall 0 R).diff
      (isOpen_biUnion fun β _ => Metric.isOpen_ball)
    have hPK : ∀ z ∈ K, P z ≠ 0 := fun z hz h => by
      have := (listDivisor_quadrantListOf_singleton_eq_zero_iff hα z).1 h
      exact hz.2 (mem_biUnion this (Metric.mem_ball_self hδ))
    obtain ⟨c₁, hc₁, hc₁K⟩ : ∃ c₁ > 0, ∀ z ∈ K, c₁ ≤ ‖P z‖ := by
      rcases K.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨1, one_pos, fun z hz => by rw [hKe] at hz; exact absurd hz (Set.notMem_empty z)⟩
      · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne
          ((differentiable_listDivisor L).continuous.norm.continuousOn)
        exact ⟨‖P z₀‖, norm_pos_iff.2 (hPK z₀ hz₀), fun z hz => hmin hz⟩
    refine ⟨min 1 (c₁ / (R ^ 2 + 1)), lt_min one_pos (by positivity), fun ε hε hεlt z hz => ?_⟩
    have hε1 : ε < 1 := hεlt.trans_le (min_le_left _ _)
    have hεc : ε * (R ^ 2 + 1) < c₁ := by
      have := hεlt.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ (by positivity)] at this
    have hPz : ‖P z‖ = ε * ‖z‖ ^ 2 := by
      rw [eq_neg_of_add_eq_zero_left hz, norm_neg, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hε.le]
    by_contra hno
    push Not at hno
    by_cases hzR : R ≤ ‖z‖
    · have := hbig z hzR
      rw [hPz] at this
      nlinarith [pow_pos (lt_of_lt_of_le one_pos (hR1.trans hzR)) 2]
    · push Not at hzR
      have hzK : z ∈ K := ⟨Metric.mem_closedBall.2 (by rw [dist_zero_right]; exact hzR.le),
        fun hmem => by
          obtain ⟨β, hβ, hzβ⟩ := mem_iUnion₂.1 hmem
          exact absurd (hno β hβ) (not_le.2 (by rwa [Metric.mem_ball, dist_eq_norm] at hzβ))⟩
      have h1 := hc₁K z hzK
      rw [hPz] at h1
      have : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR.le 2
      nlinarith

end

end RHTower
