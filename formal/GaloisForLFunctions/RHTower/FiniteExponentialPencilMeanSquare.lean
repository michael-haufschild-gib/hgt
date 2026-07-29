import GaloisForLFunctions.RHTower.GaussLattice

/-!
# Cancellation-resistant mean square for finite exponential pencils

A finite sum of distinct unit-modulus modes cannot decay to zero when one coefficient is nonzero.
The proof is quantitative: its discrete Cesaro mean-square is exactly the sum of the squared
coefficient norms. This is the finite dominant-mode input needed to read an exponential growth
radius without assuming that phases have a pointwise limit.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The discrete Cesaro mean of a unit-circle geometric progression detects exactly the constant
mode. -/
theorem tendsto_complex_geom_cesaro_of_norm_eq_one
    (w : ℂ) (hw : ‖w‖ = 1) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, w ^ m)
      atTop (nhds (if w = 1 then 1 else 0)) := by
  by_cases h : w = 1
  · subst w
    simp only [if_pos, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    norm_num [Nat.ne_of_gt hN]
  · simpa [h] using tendsto_complex_geom_cesaro_of_norm_eq_one_of_ne_one hw h

/-- A finite unit-circle exponential sum has Cesaro mean equal to the sum of its constant-mode
coefficients. -/
theorem tendsto_finset_complex_geometric_cesaro
    {ι : Type*} (s : Finset ι) (c w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ Finset.range N, ∑ i ∈ s, c i * w i ^ n)
      atTop (nhds (∑ i ∈ s, if w i = 1 then c i else 0)) := by
  have hterm (i : ι) (hi : i ∈ s) : Tendsto
      (fun N : ℕ => c i *
        (((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, w i ^ n))
      atTop (nhds (if w i = 1 then c i else 0)) := by
    convert tendsto_const_nhds.mul
      (tendsto_complex_geom_cesaro_of_norm_eq_one (w i) (hw i hi)) using 1
    all_goals split_ifs <;> simp_all
  have hsum := tendsto_finsetSum s hterm
  convert hsum using 1
  funext N
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- A finite exponential pencil. -/
def finiteExponentialPencil {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ s, c i * z i ^ n

/-- Exact complex Cesaro mean-square identity for a finite pencil with distinct unit modes. -/
theorem tendsto_finiteExponentialPencil_cesaro_star_mul
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : Set.InjOn z (s : Set ι)) :
    Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
        star (finiteExponentialPencil s c z n) * finiteExponentialPencil s c z n)
      atTop (nhds (∑ i ∈ s, star (c i) * c i)) := by
  let pairs : Finset (ι × ι) := s.product s
  let C : ι × ι → ℂ := fun p => star (c p.1) * c p.2
  let W : ι × ι → ℂ := fun p => star (z p.1) * z p.2
  have hW (p : ι × ι) (hp : p ∈ pairs) : ‖W p‖ = 1 := by
    have hp' : p.1 ∈ s ∧ p.2 ∈ s := Finset.mem_product.mp (by simpa [pairs] using hp)
    dsimp only [W]
    rw [norm_mul, norm_star, hz p.1 hp'.1, hz p.2 hp'.2, one_mul]
  have hphase (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      star (z i) * z j = 1 ↔ i = j := by
    have hui : z i * star (z i) = 1 := by
      simpa [hz i hi] using Complex.mul_conj' (z i)
    have hsi : star (z i) * z i = 1 := by
      simpa [hz i hi] using Complex.conj_mul' (z i)
    constructor
    · intro h
      exact (hinj hj hi (calc
        z j = 1 * z j := (one_mul _).symm
        _ = (z i * star (z i)) * z j := by rw [hui]
        _ = z i * (star (z i) * z j) := by rw [mul_assoc]
        _ = z i := by rw [h, mul_one])).symm
    · intro h
      subst j
      exact hsi
  have hlim := tendsto_finset_complex_geometric_cesaro pairs C W hW
  convert hlim using 1
  · funext N
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simp only [finiteExponentialPencil]
    change (starRingEnd ℂ) (∑ i ∈ s, c i * z i ^ n) *
      (∑ i ∈ s, c i * z i ^ n) = _
    rw [map_sum]
    simp_rw [map_mul, map_pow]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    simp only [pairs, C, W]
    change (∑ i ∈ s, ∑ j ∈ s,
        (starRingEnd ℂ) (c i) * (starRingEnd ℂ) (z i) ^ n *
          (c j * z j ^ n)) =
      ∑ p ∈ s ×ˢ s, star (c p.1) * c p.2 *
        (star (z p.1) * z p.2) ^ n
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [starRingEnd_apply, mul_pow]
    ring
  · apply congrArg nhds
    symm
    dsimp only [pairs, C, W]
    change (∑ p ∈ s ×ˢ s,
        if star (z p.1) * z p.2 = 1 then star (c p.1) * c p.2 else 0) =
      ∑ i ∈ s, star (c i) * c i
    rw [Finset.sum_product]
    calc
      (∑ x ∈ s, ∑ y ∈ s,
          if star (z x) * z y = 1 then star (c x) * c y else 0) =
          ∑ x ∈ s, star (c x) * c x := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_eq_single i]
            · rw [if_pos ((hphase i i hi hi).2 rfl)]
            · intro j hj hji
              rw [if_neg]
              exact fun h => hji ((hphase i j hi hj).1 h).symm
            · intro hi'
              exact (hi' hi).elim
      _ = _ := rfl

/-- Exact real Cesaro mean-square identity for a finite pencil with distinct unit modes. -/
theorem tendsto_finiteExponentialPencil_cesaro_norm_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : Set.InjOn z (s : Set ι)) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖finiteExponentialPencil s c z n‖ ^ 2)
      atTop (nhds (∑ i ∈ s, ‖c i‖ ^ 2)) := by
  have h := tendsto_finiteExponentialPencil_cesaro_star_mul s c z hz hinj
  have hre := (Complex.continuous_re.tendsto
    (∑ i ∈ s, star (c i) * c i)).comp h
  convert hre using 1
  · funext N
    change (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖finiteExponentialPencil s c z n‖ ^ 2 =
      ((((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
        star (finiteExponentialPencil s c z n) *
          finiteExponentialPencil s c z n)).re
    rw [Complex.mul_re]
    have hreN : ((((N : ℝ) : ℂ)⁻¹).re) = (N : ℝ)⁻¹ := by norm_num
    have himN : ((((N : ℝ) : ℂ)⁻¹).im) = 0 := by norm_num
    rw [hreN, himN, zero_mul, sub_zero]
    rw [← Complex.reCLM_apply, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [show star (finiteExponentialPencil s c z n) *
        finiteExponentialPencil s c z n =
        (‖finiteExponentialPencil s c z n‖ ^ 2 : ℂ) by
      simpa using Complex.conj_mul' (finiteExponentialPencil s c z n)]
    rw [Complex.reCLM_apply]
    rw [← Complex.ofReal_pow]
    exact (Complex.ofReal_re _).symm
  · apply congrArg nhds
    rw [← Complex.reCLM_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show star (c i) * c i = (‖c i‖ ^ 2 : ℂ) by
      simpa using Complex.conj_mul' (c i)]
    rw [Complex.reCLM_apply]
    rw [← Complex.ofReal_pow]
    exact (Complex.ofReal_re _).symm

/-- **Finite dominant-mode survival.** A finite pencil of distinct unit modes with one nonzero
coefficient cannot tend to zero. This is the cancellation-resistant replacement for selecting a
pointwise dominant phase. -/
theorem not_tendsto_finiteExponentialPencil_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : Set.InjOn z (s : Set ι))
    (hc : ∃ i ∈ s, c i ≠ 0) :
    ¬ Tendsto (finiteExponentialPencil s c z) atTop (nhds 0) := by
  intro hzero
  have hnorm : Tendsto (fun n => ‖finiteExponentialPencil s c z n‖ ^ 2)
      atTop (nhds 0) := by
    simpa using hzero.norm.pow 2
  have hcesaro := hnorm.cesaro
  have henergy := tendsto_finiteExponentialPencil_cesaro_norm_sq s c z hz hinj
  have heq := tendsto_nhds_unique henergy hcesaro
  have hpos : 0 < ∑ i ∈ s, ‖c i‖ ^ 2 := by
    apply Finset.sum_pos' (fun i hi => sq_nonneg _)
    obtain ⟨i, hi, hci⟩ := hc
    exact ⟨i, hi, sq_pos_of_pos (norm_pos_iff.mpr hci)⟩
  linarith

end

end RHTower

namespace RHTower

noncomputable section

/-- Sum of the coefficients in one mode fiber of a finite exponential pencil. -/
def finiteExponentialFiberCoefficient {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (z : ι → ℂ) (u : ℂ) : ℂ :=
  ∑ i ∈ s with z i = u, c i

/-- Collapsing equal modes and adding their coefficients does not change a finite pencil. -/
theorem finiteExponentialPencil_image_eq
    {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (n : ℕ) :
    finiteExponentialPencil (s.image z)
        (finiteExponentialFiberCoefficient s c z) id n =
      finiteExponentialPencil s c z n := by
  classical
  rw [finiteExponentialPencil, finiteExponentialPencil]
  calc
    (∑ u ∈ s.image z, finiteExponentialFiberCoefficient s c z u * id u ^ n) =
        ∑ u ∈ s.image z, ∑ i ∈ s with z i = u, c i * z i ^ n := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [finiteExponentialFiberCoefficient, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          have hziu : z i = u := (Finset.mem_filter.mp hi).2
          simp only [id_eq]
          rw [hziu]
    _ = ∑ i ∈ s, c i * z i ^ n :=
      Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem z hi) (fun i => c i * z i ^ n)

/-- **Repeated-mode dominant survival.** A finite unit-modulus pencil cannot decay when one
aggregated mode coefficient is nonzero. Equal Xi multiplicity copies or reflected reciprocal-square
values therefore reinforce rather than evade the mean-square obstruction. -/
theorem not_tendsto_finiteExponentialPencil_zero_of_fiberCoefficient
    {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hc : ∃ u ∈ s.image z, finiteExponentialFiberCoefficient s c z u ≠ 0) :
    ¬ Tendsto (finiteExponentialPencil s c z) atTop (nhds 0) := by
  classical
  intro hzero
  have hzeroImage : Tendsto
      (finiteExponentialPencil (s.image z)
        (finiteExponentialFiberCoefficient s c z) id) atTop (nhds 0) := by
    apply hzero.congr'
    exact Eventually.of_forall fun n => (finiteExponentialPencil_image_eq s c z n).symm
  apply (not_tendsto_finiteExponentialPencil_zero
    (s.image z) (finiteExponentialFiberCoefficient s c z) id) ?_ ?_ hc hzeroImage
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact hz i hi
  · intro u hu v hv huv
    exact huv

end

end RHTower

namespace RHTower

noncomputable section

/-- Unit scalar aligning the nonzero complex vector `y` with the nonzero vector `x`. -/
def complexAlignmentUnit (x y : ℂ) : ℂ :=
  (x / (‖x‖ : ℂ)) * (star y / (‖y‖ : ℂ))

@[simp] theorem norm_complexAlignmentUnit {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖complexAlignmentUnit x y‖ = 1 := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  simp [complexAlignmentUnit, hnx.ne', hny.ne']

/-- The alignment unit makes the triangle inequality exact. -/
theorem norm_add_mul_complexAlignmentUnit {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x + y * complexAlignmentUnit x y‖ = ‖x‖ + ‖y‖ := by
  have hnx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hny0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hyy : y * star y = (‖y‖ ^ 2 : ℂ) := by
    simpa using Complex.mul_conj' y
  have halign : x + y * complexAlignmentUnit x y =
      (((‖x‖ + ‖y‖) / ‖x‖ : ℝ) : ℂ) * x := by
    rw [complexAlignmentUnit]
    rw [show y * (x / (‖x‖ : ℂ) * (star y / (‖y‖ : ℂ))) =
        ((‖y‖ / ‖x‖ : ℝ) : ℂ) * x by
      field_simp [hnx0, hny0]
      rw [hyy]
      push_cast
      field_simp [hnx0, hny0]]
    push_cast
    field_simp [hnx0]
  rw [halign, norm_mul, Complex.norm_real]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsum : 0 ≤ ‖x‖ + ‖y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum hnx.le)]
  field_simp [hnx.ne']

/-- A nonreal affine node has a unit-circle pencil value strictly outside the closed unit disk. -/
theorem exists_unit_norm_one_sub_add_mul_gt_one {a : ℂ} (him : a.im ≠ 0) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ 1 < ‖1 - a + a * w‖ := by
  have ha : a ≠ 0 := by intro h; subst a; simp at him
  have h1a : 1 - a ≠ 0 := by
    intro h
    have : a = 1 := (sub_eq_zero.mp h).symm
    subst a
    simp at him
  let w := complexAlignmentUnit (1 - a) a
  refine ⟨w, norm_complexAlignmentUnit h1a ha, ?_⟩
  rw [norm_add_mul_complexAlignmentUnit h1a ha]
  have htri : (1 : ℝ) ≤ ‖1 - a‖ + ‖a‖ := by
    have h := norm_add_le (1 - a) a
    norm_num at h ⊢
    exact h
  apply lt_of_le_of_ne htri
  intro heq
  have hadd : ‖(1 - a) + a‖ = ‖1 - a‖ + ‖a‖ := by
    simpa using heq
  have hparallel := norm_add_eq_iff_real.mp hadd
  have himEq := congrArg Complex.im hparallel
  simp only [Complex.smul_im, Complex.sub_im, Complex.one_im, smul_eq_mul] at himEq
  have hnx : 0 < ‖1 - a‖ := norm_pos_iff.mpr h1a
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hfac : (‖a‖ + ‖1 - a‖) * a.im = 0 := by linarith
  have hsumne : ‖a‖ + ‖1 - a‖ ≠ 0 := ne_of_gt (add_pos hna hnx)
  exact him ((mul_eq_zero.mp hfac).resolve_left hsumne)

end

end RHTower

namespace RHTower

noncomputable section

/-- **Dominant finite packet versus summable tail.** If a norm-summable countable pencil has a
finite set of maximal-radius modes, all remaining modes lie strictly inside that radius, and one
maximal mode fiber has nonzero aggregate coefficient, then the pencil divided by the maximal
radius cannot tend to zero. The complement is killed by dominated convergence; the maximal packet
survives by the finite Cesaro mean-square identity. -/
theorem not_tendsto_tsum_normalizedExponentialPencil_zero_of_dominantFinset
    {ι : Type*} (c b : ι → ℂ) (hc : Summable c)
    (D : Finset ι) {r : ℝ} (hr : 0 < r)
    (hdom : ∀ i ∈ D, ‖b i‖ = r)
    (hsub : ∀ i ∉ D, ‖b i‖ < r)
    (hfiber : ∃ u ∈ D.image (fun i => b i / (r : ℂ)),
      finiteExponentialFiberCoefficient D c (fun i => b i / (r : ℂ)) u ≠ 0) :
    ¬ Tendsto
      (fun n : ℕ => ∑' i : ι, c i * (b i / (r : ℂ)) ^ n)
      atTop (nhds 0) := by
  classical
  let z : ι → ℂ := fun i => b i / (r : ℂ)
  have hzle (i : ι) : ‖z i‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hble : ‖b i‖ ≤ r := by
      by_cases hi : i ∈ D
      · rw [hdom i hi]
      · exact (hsub i hi).le
    exact (div_le_one hr).2 hble
  have hsum (n : ℕ) : Summable (fun i : ι => c i * z i ^ n) := by
    apply hc.norm.of_norm_bounded
    intro i
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg (c i))
      (pow_le_one₀ (norm_nonneg (z i)) (hzle i))
  have htail : Tendsto
      (fun n : ℕ => ∑' i : {i // i ∉ D}, c i * z i ^ n)
      atTop (nhds 0) := by
    have hbound : Summable (fun i : {i // i ∉ D} => ‖c i‖) :=
      hc.norm.subtype _
    have hpoint (i : {i // i ∉ D}) :
        Tendsto (fun n : ℕ => c i * z i ^ n) atTop (nhds 0) := by
      have hzlt : ‖z i‖ < 1 := by
        dsimp only [z]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        exact (div_lt_one hr).2 (hsub i i.2)
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hzlt)
    have hdominated : ∀ᶠ n : ℕ in atTop, ∀ i : {i // i ∉ D},
        ‖c i * z i ^ n‖ ≤ ‖c i‖ := by
      exact Eventually.of_forall fun n i => by
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg (c i))
          (pow_le_one₀ (norm_nonneg (z i)) (hzle i))
    simpa using tendsto_tsum_of_dominated_convergence hbound hpoint hdominated
  have hsplit (n : ℕ) :
      finiteExponentialPencil D c z n +
          (∑' i : {i // i ∉ D}, c i * z i ^ n) =
        ∑' i : ι, c i * z i ^ n := by
    simpa only [finiteExponentialPencil] using
      (hsum n).sum_add_tsum_subtype_compl D
  intro hfull
  have hdomzero : Tendsto (finiteExponentialPencil D c z) atTop (nhds 0) := by
    have hfull' : Tendsto (fun n : ℕ => ∑' i : ι, c i * z i ^ n)
        atTop (nhds 0) := by simpa only [z] using hfull
    have hdiff := hfull'.sub htail
    simpa using hdiff.congr' (Eventually.of_forall fun n => by
      rw [← hsplit n]
      ring)
  have hzD : ∀ i ∈ D, ‖z i‖ = 1 := by
    intro i hi
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hdom i hi]
    exact div_self hr.ne'
  exact (not_tendsto_finiteExponentialPencil_zero_of_fiberCoefficient D c z
    hzD hfiber) hdomzero

/-- **Finite maximal-radius extraction.** If a countable family of complex modes converges to
the unit mode off finite sets and one mode lies strictly outside the unit circle, then its global
maximal radius is greater than one and is attained on a nonempty finite packet. Every mode outside
that packet has strictly smaller radius. -/
theorem exists_finite_maximal_norm_packet_of_tendsto_cofinite_one
    {ι : Type*} (b : ι → ℂ)
    (hb : Tendsto b cofinite (nhds 1)) {i0 : ι} (hi0 : 1 < ‖b i0‖) :
    ∃ D : Finset ι, ∃ r : ℝ,
      1 < r ∧ D.Nonempty ∧
        (∀ i ∈ D, ‖b i‖ = r) ∧ (∀ i ∉ D, ‖b i‖ < r) := by
  classical
  let a : ℝ := (1 + ‖b i0‖) / 2
  have ha1 : 1 < a := by dsimp [a]; linarith
  have hai0 : a < ‖b i0‖ := by dsimp [a]; linarith
  have hev : ∀ᶠ i : ι in cofinite, b i ∈ Metric.ball (1 : ℂ) (a - 1) :=
    hb (Metric.ball_mem_nhds _ (sub_pos.mpr ha1))
  have hbad : {i : ι | b i ∉ Metric.ball (1 : ℂ) (a - 1)}.Finite := by
    have hfin := Filter.mem_cofinite.mp (Filter.eventually_iff.mp hev)
    simpa only [Set.compl_setOf] using hfin
  have hsuper : {i : ι | a ≤ ‖b i‖}.Finite := by
    apply hbad.subset
    intro i hi hball
    change a ≤ ‖b i‖ at hi
    have hdist : ‖b i - 1‖ < a - 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hball
    have htri : ‖b i‖ ≤ ‖b i - 1‖ + 1 := by
      calc
        ‖b i‖ = ‖(b i - 1) + 1‖ := by ring_nf
        _ ≤ ‖b i - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖b i - 1‖ + 1 := by norm_num
    linarith
  let S : Finset ι := hsuper.toFinset
  have hi0S : i0 ∈ S := by
    simp only [S, Set.Finite.mem_toFinset]
    exact hai0.le
  have hSne : S.Nonempty := ⟨i0, hi0S⟩
  obtain ⟨q, hqS, hqmax⟩ := Finset.exists_max_image S (fun i => ‖b i‖) hSne
  let r : ℝ := ‖b q‖
  let D : Finset ι := S.filter (fun i => ‖b i‖ = r)
  have hri0 : ‖b i0‖ ≤ r := hqmax i0 hi0S
  have hr1 : 1 < r := lt_of_lt_of_le hi0 hri0
  have hqD : q ∈ D := by simp [D, r, hqS]
  refine ⟨D, r, hr1, ⟨q, hqD⟩, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hiD
    by_cases hi : a ≤ ‖b i‖
    · have hiS : i ∈ S := by
        dsimp only [S]
        rw [Set.Finite.mem_toFinset]
        change a ≤ ‖b i‖
        exact hi
      have hir : ‖b i‖ ≤ r := hqmax i hiS
      exact lt_of_le_of_ne hir (fun heq => hiD (by simp [D, hiS, heq]))
    · have hia : ‖b i‖ < a := lt_of_not_ge hi
      have hai0le : a ≤ ‖b i0‖ := hai0.le
      exact lt_of_lt_of_le hia (hai0le.trans hri0)

end

end RHTower
