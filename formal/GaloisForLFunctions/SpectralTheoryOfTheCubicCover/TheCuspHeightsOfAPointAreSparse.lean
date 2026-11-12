import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheIncompleteEisensteinSeriesReadsTheConstantTerm

/-!
# The cusp heights of a point are sparse

For a point `w` of hyperbolic three-space, the heights `v_x(w)` of `w` seen from the cusp cosets
`x ∈ Γ∞\Γ` of the level-three group are sparse: at most `K Y^{−2}` of them are `≥ Y`, for every
`0 < Y ≤ 1` (`card_cuspCosets_height_le`), with `K` absolute.

* `card_lattice_disc_le` (**lattice points in a disc**): a finite set of points of `ℤ[ω]` within
  distance `R` of `a` has at most `π(3R + δ)²/|P|` elements: the translates of the period
  parallelogram `P` of `3ℤ[ω]` by the points are disjoint and lie in a disc of radius `3R + δ`.
* The count: move `w` by `M₀ ∈ SL₂(ℤ[ω])` to `w₀ = z₀ + jv₀` with `v₀ ≥ √(2/3)` (Ford reduction,
  MMD). The coset `x = Γ∞N` has height `v₀/(|c z₀ + d|² + |c|² v₀²)` with `(c, d)` the bottom row of
  `N M₀⁻¹`, injective in `x`. Height `≥ Y` forces `|c|² ≤ 1/(v₀Y)` and `|c z₀ + d|² ≤ v₀/Y`; rows with
  `c = 0` have `d` a unit, and rows with `c ≠ 0` need `v₀ ≤ 1/Y`, so the count is
  `≤ L(1) + L(R₁)L(R₂)` with `R₁²R₂² = 1/Y²`.

This is the multiplicity bound of the period strip in the quotient: it turns the square integrability
of an automorphic function into bounds for its Fourier coefficients (Hecke bound).
-/

noncomputable section

open MeasureTheory Function
open scoped BigOperators Classical MatrixGroups ENNReal Pointwise

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### Lattice points in a disc -/

/-- The radius bound `δ = Σ‖b_i‖` of the period parallelogram. -/
abbrev periodRadius : ℝ := ∑ i : Fin 2, ‖periodBasis i‖

theorem periodRadius_nonneg : 0 ≤ periodRadius := Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **Lattice points in a disc.** `|S| · |P| ≤ π (3R + δ)²` for every finite set `S ⊆ ℤ[ω]` within
distance `R` of `a`. -/
theorem card_lattice_disc_le (a : ℂ) {R : ℝ} (hR : 0 ≤ R) (S : Finset O)
    (hS : ∀ d ∈ S, ‖ringComplex d - a‖ ≤ R) :
    (S.card : ℝ) * (9 * Real.sqrt 3 / 2) ≤ Real.pi * (3 * R + periodRadius) ^ 2 := by
  set F : O → Set ℂ := fun d => periodPoint d +ᵥ periodDomain with hF
  have hdisj : Set.Pairwise (S : Set O) (AEDisjoint volume on F) := by
    intro d₁ _ d₂ _ hne
    exact periodDomain_fundamental.aedisjoint (fun h => hne (periodPoint_bijective.1 h))
  have hmeas : ∀ d ∈ S, NullMeasurableSet (F d) volume := fun d _ =>
    periodDomain_fundamental.nullMeasurableSet_vadd (periodPoint d)
  have hsub : (⋃ d ∈ S, F d) ⊆ Metric.closedBall (3 * a) (3 * R + periodRadius) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨p, hp, rfl⟩ := Set.mem_vadd_set.mp hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := hS d hd
    have h2 := norm_mem_periodDomain p hp
    have he : (periodPoint d +ᵥ p) - 3 * a = 3 * (ringComplex d - a) + p := by
      change (↑(periodPoint d) + p) - 3 * a = _
      rw [periodPoint_val]
      ring
    rw [he]
    calc ‖3 * (ringComplex d - a) + p‖ ≤ ‖3 * (ringComplex d - a)‖ + ‖p‖ := norm_add_le _ _
      _ = 3 * ‖ringComplex d - a‖ + ‖p‖ := by rw [norm_mul]; norm_num
      _ ≤ 3 * R + periodRadius := by linarith
  have hvol := measure_biUnion_finset₀ hdisj hmeas
  have hle := measure_mono (μ := volume) hsub
  rw [hvol] at hle
  simp only [hF, measure_vadd, periodDomain_volume, Finset.sum_const, nsmul_eq_mul,
    Complex.volume_closedBall] at hle
  have hA : (0 : ℝ) ≤ 9 * Real.sqrt 3 / 2 := by positivity
  have hB : (0 : ℝ) ≤ 3 * R + periodRadius := by linarith [periodRadius_nonneg]
  have hL : ((S.card : ℝ≥0∞) * ENNReal.ofReal (9 * Real.sqrt 3 / 2)) =
      ENNReal.ofReal ((S.card : ℝ) * (9 * Real.sqrt 3 / 2)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hRhs : ENNReal.ofReal (3 * R + periodRadius) ^ 2 * (NNReal.pi : ℝ≥0∞) =
      ENNReal.ofReal (Real.pi * (3 * R + periodRadius) ^ 2) := by
    rw [← ENNReal.ofReal_pow hB, mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_mul Real.pi_pos.le]
  rw [hL, hRhs] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle

/-- The constant `c₀` of the lattice count `|S| ≤ c₀ (1 + R²)`. -/
abbrev latticeConst : ℝ := Real.pi * (18 + 2 * periodRadius ^ 2) / (9 * Real.sqrt 3 / 2)

theorem latticeConst_nonneg : 0 ≤ latticeConst := by positivity

/-- `|S| ≤ c₀ (1 + R²)` for every finite set `S ⊆ ℤ[ω]` within distance `R` of `a`. -/
theorem card_lattice_disc_le' (a : ℂ) {R : ℝ} (hR : 0 ≤ R) (S : Finset O)
    (hS : ∀ d ∈ S, ‖ringComplex d - a‖ ≤ R) :
    (S.card : ℝ) ≤ latticeConst * (1 + R ^ 2) := by
  have h := card_lattice_disc_le a hR S hS
  have hA : (0 : ℝ) < 9 * Real.sqrt 3 / 2 := by positivity
  have hsq : (3 * R + periodRadius) ^ 2 ≤ (18 + 2 * periodRadius ^ 2) * (1 + R ^ 2) := by
    nlinarith [sq_nonneg (3 * R - periodRadius), sq_nonneg periodRadius, sq_nonneg R]
  rw [latticeConst, div_mul_eq_mul_div, le_div_iff₀ hA]
  calc (S.card : ℝ) * (9 * Real.sqrt 3 / 2) ≤ Real.pi * (3 * R + periodRadius) ^ 2 := h
    _ ≤ Real.pi * ((18 + 2 * periodRadius ^ 2) * (1 + R ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
    _ = _ := by ring

/-! ### The heights of a point -/

/-- The absolute constant `K` of the height count. -/
abbrev heightCountConst : ℝ := 2 * latticeConst + 5 * latticeConst ^ 2

/-- The bottom row of `N M₀⁻¹` for a representative `N` of the coset `x`. -/
def shiftedRow (M₀ : SL(2, O)) (x : CuspCosets) : SL(2, O) := ((Quotient.out x : levelThree) : SL(2, O)) * M₀⁻¹

theorem shiftedRow_injective (M₀ : SL(2, O)) {x y : CuspCosets}
    (h0 : shiftedRow M₀ x 1 0 = shiftedRow M₀ y 1 0) (h1 : shiftedRow M₀ x 1 1 = shiftedRow M₀ y 1 1) :
    x = y := by
  have hrow : ∀ j : Fin 2, ((Quotient.out x : levelThree) : SL(2, O)) 1 j =
      ((Quotient.out y : levelThree) : SL(2, O)) 1 j := by
    intro j
    have hx : ((Quotient.out x : levelThree) : SL(2, O)) = shiftedRow M₀ x * M₀ := by
      simp [shiftedRow]
    have hy : ((Quotient.out y : levelThree) : SL(2, O)) = shiftedRow M₀ y * M₀ := by
      simp [shiftedRow]
    rw [hx, hy]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  change cosetOf _ = cosetOf _
  apply cosetRow_injective
  simp only [cosetRow_cosetOf]
  funext j
  exact hrow j

/-- The height of `w` from the coset `x`, through the reduced point `M₀ w = z₀ + jv₀`. -/
theorem cosetHeight_eq (M₀ : SL(2, O)) (w : HyperbolicSpace) (z₀ : ℂ) (v₀ : ℝ) (hv₀ : 0 < v₀)
    (hM : integralComplexMatrix M₀ • w = upperPoint z₀ v₀ hv₀) (x : CuspCosets) :
    cosetHeight x w = v₀ / (‖ringComplex (shiftedRow M₀ x 1 0) * z₀ +
      ringComplex (shiftedRow M₀ x 1 1)‖ ^ 2 + ‖ringComplex (shiftedRow M₀ x 1 0)‖ ^ 2 * v₀ ^ 2) := by
  have hw : w = integralComplexMatrix M₀⁻¹ • upperPoint z₀ v₀ hv₀ := by
    rw [← hM, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  conv_lhs => rw [← Quotient.out_eq x]
  change cosetHeight (cosetOf (Quotient.out x)) w = _
  rw [cosetHeight_cosetOf, hw, ← mul_smul, ← integralComplexMatrix_levelThree, ← map_mul,
    hyperbolicHeight_action_upperPoint]
  rfl

/-- **The cusp heights of a point are sparse.** For every `w` and `0 < Y ≤ 1`, a finite set of cusp
cosets on which `w` has height `≥ Y` has at most `K/Y²` elements. -/
theorem card_cuspCosets_height_le (w : HyperbolicSpace) {Y : ℝ} (hY : 0 < Y) (hY1 : Y ≤ 1)
    (s : Finset CuspCosets) (hs : ∀ x ∈ s, Y ≤ cosetHeight x w) :
    (s.card : ℝ) ≤ heightCountConst / Y ^ 2 := by
  obtain ⟨M₀, z₀, v₀, hv₀, hM, -, hfloor⟩ := bianchi_reduction_height_floor w
  set c : CuspCosets → O := fun x => shiftedRow M₀ x 1 0 with hc
  set d : CuspCosets → O := fun x => shiftedRow M₀ x 1 1 with hd
  -- the denominator bound
  have hden : ∀ x ∈ s, ‖ringComplex (c x) * z₀ + ringComplex (d x)‖ ^ 2 +
      ‖ringComplex (c x)‖ ^ 2 * v₀ ^ 2 ≤ v₀ / Y := by
    intro x hx
    have hh := hs x hx
    rw [cosetHeight_eq M₀ w z₀ v₀ hv₀ hM x] at hh
    have hpos : 0 < ‖ringComplex (c x) * z₀ + ringComplex (d x)‖ ^ 2 +
        ‖ringComplex (c x)‖ ^ 2 * v₀ ^ 2 := by
      by_contra hn
      have h0 : ‖ringComplex (c x) * z₀ + ringComplex (d x)‖ ^ 2 +
          ‖ringComplex (c x)‖ ^ 2 * v₀ ^ 2 = 0 :=
        le_antisymm (not_lt.mp hn) (by positivity)
      rw [h0, div_zero] at hh
      linarith
    rw [le_div_iff₀ hpos] at hh
    rw [le_div_iff₀ hY]
    linarith
  have hv0 : 0 < Real.sqrt (2 / 3) := Real.sqrt_pos.mpr (by norm_num)
  -- rows with `c = 0`: the entry `d` is a unit
  set s₀ := s.filter (fun x => c x = 0) with hs₀
  set s₁ := s.filter (fun x => c x ≠ 0) with hs₁
  have hsplit : s.card = s₀.card + s₁.card := by
    rw [hs₀, hs₁, ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not s s _),
      Finset.filter_union_filter_not_eq]
  have hcard0 : (s₀.card : ℝ) ≤ 2 * latticeConst := by
    have hinj : Set.InjOn d s₀ := by
      intro x hx y hy h
      have hx0 : c x = 0 := (Finset.mem_filter.mp hx).2
      have hy0 : c y = 0 := (Finset.mem_filter.mp hy).2
      exact shiftedRow_injective M₀ (by simpa [hc] using hx0.trans hy0.symm) h
    rw [← Finset.card_image_of_injOn hinj]
    have h := card_lattice_disc_le' 0 zero_le_one (s₀.image d) (by
      intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
      have hx0 : c x = 0 := (Finset.mem_filter.mp hx).2
      have hdet := (shiftedRow M₀ x).property
      rw [Matrix.det_fin_two] at hdet
      have hcx : shiftedRow M₀ x 1 0 = 0 := hx0
      rw [hcx, mul_zero, sub_zero] at hdet
      have ha : shiftedRow M₀ x 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
      have hd0 : shiftedRow M₀ x 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
      have hn := congrArg (fun t => Complex.normSq (ringComplex t)) hdet
      simp only [map_mul, map_one] at hn
      have h1 := one_le_normSq_embedding _ ha
      have h2 := one_le_normSq_embedding _ hd0
      have hle : Complex.normSq (ringComplex (shiftedRow M₀ x 1 1)) ≤ 1 := by nlinarith
      rw [Complex.normSq_eq_norm_sq] at hle
      have hdx : d x = shiftedRow M₀ x 1 1 := rfl
      rw [sub_zero, hdx]
      nlinarith [norm_nonneg (ringComplex (shiftedRow M₀ x 1 1))])
    norm_num at h
    linarith
  -- rows with `c ≠ 0` force `v₀ ≤ 1/Y`
  have hcard1 : (s₁.card : ℝ) ≤ latticeConst ^ 2 * (5 / Y ^ 2) := by
    rcases s₁.eq_empty_or_nonempty with he | ⟨x₁, hx₁⟩
    · rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
    have hvY : v₀ ≤ 1 / Y := by
      have hx := Finset.mem_filter.mp hx₁
      have hden1 := hden x₁ hx.1
      have hc1 := one_le_normSq_embedding _ hx.2
      rw [Complex.normSq_eq_norm_sq] at hc1
      rw [le_div_iff₀ hY] at hden1 ⊢
      have hA0 : 0 ≤ ‖ringComplex (c x₁) * z₀ + ringComplex (d x₁)‖ ^ 2 * Y := by positivity
      have hB := mul_le_mul_of_nonneg_right hc1 (by positivity : (0 : ℝ) ≤ v₀ ^ 2 * Y)
      have h3 : v₀ * (v₀ * Y) ≤ v₀ * 1 := by nlinarith
      exact le_of_mul_le_mul_left h3 hv₀
    set R₁ := Real.sqrt (1 / (v₀ * Y)) with hR₁
    set R₂ := Real.sqrt (v₀ / Y) with hR₂
    have hcR : ∀ x ∈ s₁, ‖ringComplex (c x) - 0‖ ≤ R₁ := by
      intro x hx
      rw [sub_zero]
      apply Real.le_sqrt_of_sq_le
      have h := hden x (Finset.mem_filter.mp hx).1
      rw [le_div_iff₀ (mul_pos hv₀ hY)]
      have : ‖ringComplex (c x)‖ ^ 2 * v₀ ^ 2 ≤ v₀ / Y := by nlinarith [sq_nonneg (‖ringComplex (c x) * z₀ + ringComplex (d x)‖)]
      rw [le_div_iff₀ hY] at this
      nlinarith
    have hdR : ∀ x ∈ s₁, ‖ringComplex (d x) - (-(ringComplex (c x) * z₀))‖ ≤ R₂ := by
      intro x hx
      apply Real.le_sqrt_of_sq_le
      have h := hden x (Finset.mem_filter.mp hx).1
      rw [sub_neg_eq_add, add_comm]
      nlinarith [sq_nonneg (‖ringComplex (c x)‖ * v₀)]
    -- fibers over `c`
    rw [Finset.card_eq_sum_card_image c s₁]
    have hfib : ∀ e ∈ s₁.image c, ((s₁.filter (fun x => c x = e)).card : ℝ) ≤
        latticeConst * (1 + R₂ ^ 2) := by
      intro e he
      have hinj : Set.InjOn d (s₁.filter (fun x => c x = e)) := by
        intro x hx y hy h
        have hxe : c x = e := (Finset.mem_filter.mp hx).2
        have hye : c y = e := (Finset.mem_filter.mp hy).2
        exact shiftedRow_injective M₀ (by simpa [hc] using hxe.trans hye.symm) h
      rw [← Finset.card_image_of_injOn hinj]
      apply card_lattice_disc_le' (-(ringComplex e * z₀)) (Real.sqrt_nonneg _)
      intro t ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      have hxe : c x = e := (Finset.mem_filter.mp hx).2
      have := hdR x (Finset.mem_filter.mp hx).1
      rwa [hxe] at this
    have himg : ((s₁.image c).card : ℝ) ≤ latticeConst * (1 + R₁ ^ 2) :=
      card_lattice_disc_le' 0 (Real.sqrt_nonneg _) (s₁.image c) (by
        intro e he
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
        exact hcR x hx)
    have hsum : ((∑ e ∈ s₁.image c, (s₁.filter (fun x => c x = e)).card : ℕ) : ℝ) ≤
        latticeConst * (1 + R₁ ^ 2) * (latticeConst * (1 + R₂ ^ 2)) := by
      push_cast
      calc ∑ e ∈ s₁.image c, ((s₁.filter (fun x => c x = e)).card : ℝ)
          ≤ ∑ _e ∈ s₁.image c, latticeConst * (1 + R₂ ^ 2) := Finset.sum_le_sum hfib
        _ = ((s₁.image c).card : ℝ) * (latticeConst * (1 + R₂ ^ 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right himg (by positivity)
    refine hsum.trans ?_
    have hR₁sq : R₁ ^ 2 = 1 / (v₀ * Y) := Real.sq_sqrt (by positivity)
    have hR₂sq : R₂ ^ 2 = v₀ / Y := Real.sq_sqrt (by positivity)
    rw [hR₁sq, hR₂sq]
    have hY2 : 0 < Y ^ 2 := by positivity
    have hexp : (1 + 1 / (v₀ * Y)) * (1 + v₀ / Y) = 1 + 1 / (v₀ * Y) + v₀ / Y + 1 / Y ^ 2 := by
      field_simp
      ring
    have h1 : 1 ≤ 1 / Y ^ 2 := by rw [le_div_iff₀ hY2]; nlinarith
    have h2 : 1 / (v₀ * Y) ≤ 2 / Y ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hY2]
      have hs2 : Real.sqrt (2 / 3) * Real.sqrt (2 / 3) = 2 / 3 := Real.mul_self_sqrt (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hfloor hY.le]
    have h3 : v₀ / Y ≤ 1 / Y ^ 2 := by
      rw [div_le_div_iff₀ hY hY2]
      rw [le_div_iff₀ hY] at hvY
      nlinarith
    calc latticeConst * (1 + 1 / (v₀ * Y)) * (latticeConst * (1 + v₀ / Y))
        = latticeConst ^ 2 * ((1 + 1 / (v₀ * Y)) * (1 + v₀ / Y)) := by ring
      _ ≤ latticeConst ^ 2 * (5 / Y ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hexp]
          have : (5 : ℝ) / Y ^ 2 = 1 / Y ^ 2 + 2 / Y ^ 2 + 1 / Y ^ 2 + 1 / Y ^ 2 := by ring
          linarith
  have hY2 : 0 < Y ^ 2 := by positivity
  have h1 : 1 ≤ 1 / Y ^ 2 := by rw [le_div_iff₀ hY2]; nlinarith
  rw [hsplit, Nat.cast_add, heightCountConst]
  have hL := latticeConst_nonneg
  calc (s₀.card : ℝ) + s₁.card ≤ 2 * latticeConst + latticeConst ^ 2 * (5 / Y ^ 2) :=
        add_le_add hcard0 hcard1
    _ ≤ 2 * latticeConst * (1 / Y ^ 2) + latticeConst ^ 2 * (5 / Y ^ 2) := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * latticeConst)
        linarith
    _ = (2 * latticeConst + 5 * latticeConst ^ 2) / Y ^ 2 := by ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
