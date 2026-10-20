import GaloisForLFunctions.SquareRootThreshold.RelaxedHodgeExponentOfPeriodicConfigurations

/-!
# Depth tomography at twice the Nyquist aperture

How much aperture does the Weil form need to *read* a periodic off-line configuration, depths and
ordinates included? A pattern of `P` reflected pairs per period `2π/ℓ` has Nyquist aperture
`Pℓ/2`, and below it the depth of a crystal is unreadable
(`crystal_weil_eq_below_nyquist`: crystals of any two depths have the same Weil form there).

**Tomography** (`depthTomography`). Two periodic off-line patterns with `P` and `P'` pairs per
period that agree on every test of an aperture `a` with `⌈2a/ℓ⌉ ≥ P + P' + 1` have the same pairs
`(depth, ordinate class)`: for every pair `(d_r, θ_r)` of the first there is a pair of the second
with `d'_{r'} = d_r` and `θ'_{r'} ≡ θ_r mod 1`. For `P' = P` the aperture is `Pℓ`, twice the Nyquist
aperture.

The mechanism:
* agreement on tests of aperture `a` is agreement of the symbols on `|m| < ⌈2a/ℓ⌉`
  (`symbol_eq_of_weil_eq`, universal lag-point tests and vanishing Hermitian Toeplitz forms);
* the symbol is a two-sided exponential moment sequence
  `D(m) = Σ_r (λ_r^m + μ_r^m)`, `λ_r = e^{d_rℓ + 2πiθ_r}`, `μ_r = e^{−d_rℓ + 2πiθ_r}`
  (`patternSymbol_eq_nodes`);
* `2N + 1` consecutive two-sided moments determine a family of at most `2N + 1` nonzero nodes with
  multiplicity (`card_fiber_eq_of_moments_eq`, Lagrange interpolation after the shift by `N`);
* the nodes off the unit circle with modulus `> 1` are the `λ_r`, which carry depth and ordinate.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Agreement of Weil forms is agreement of symbols -/

/-- Two lag-lattice configurations of the same lag `ℓ` that agree on every test of aperture `a`
have the same symbol on `|m| < ⌈2a/ℓ⌉`. -/
theorem symbol_eq_of_weil_eq (Z₁ Z₂ : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) {D₁ D₂ : ℤ → ℂ}
    (hD₁ : ∀ m, D₁ (-m) = conj (D₁ m)) (hD₂ : ∀ m, D₂ (-m) = conj (D₂ m)) {a : ℝ} (ha : 0 < a)
    (hW₁ : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      Z₁.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D₁ m)
    (hW₂ : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      Z₂.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D₂ m)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z₁.W f f = Z₂.W f f)
    {m : ℤ} (hm : |m| < ⌈2 * a / ℓ⌉₊) : D₁ m = D₂ m := by
  have hE : ∀ c₀ : Fin ⌈2 * a / ℓ⌉₊ → ℂ,
      toeplitzForm (fun m => D₁ m - D₂ m) ⌈2 * a / ℓ⌉₊ c₀ = 0 := by
    intro c₀
    obtain ⟨f, hf, hfs, B, hB, hlag⟩ := exists_bumpTest_universal hℓ ha c₀
    have h1 := h f hf hfs
    rw [hW₁ f hf hfs, hW₂ f hf hfs, hlag, hlag] at h1
    have hℓB : ((ℓ : ℝ) : ℂ) * (B : ℂ) ≠ 0 := by
      have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
      have : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
      positivity
    rw [toeplitzForm_sub, sub_eq_zero]
    refine mul_left_cancel₀ hℓB ?_
    rw [mul_assoc, mul_assoc]
    exact h1
  have hherm : ∀ m, (fun m => D₁ m - D₂ m) (-m) = conj ((fun m => D₁ m - D₂ m) m) := fun m => by
    simp only [hD₁, hD₂, map_sub]
  exact sub_eq_zero.mp (eq_zero_of_toeplitzForm_eq_zero hherm hE hm)

/-! ### Two-sided exponential moments determine their nodes -/

/-- **Two-sided moments determine nodes with multiplicity.** If two families of nonzero numbers,
of total size at most `2N + 1`, have the same moments `Σ x_i^m` for `|m| ≤ N`, every value is taken
equally often in both. -/
theorem card_fiber_eq_of_moments_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → ℂ)
    (y : κ → ℂ) (hx : ∀ i, x i ≠ 0) (hy : ∀ j, y j ≠ 0) {N : ℕ}
    (hcard : Fintype.card ι + Fintype.card κ ≤ 2 * N + 1)
    (hM : ∀ m : ℤ, |m| ≤ N → ∑ i, x i ^ m = ∑ j, y j ^ m) (v : ℂ) :
    (Finset.univ.filter fun i => x i = v).card = (Finset.univ.filter fun j => y j = v).card := by
  classical
  set V : Finset ℂ := Finset.univ.image x ∪ Finset.univ.image y with hV
  have hVcard : V.card ≤ 2 * N + 1 := by
    refine (Finset.card_union_le _ _).trans ?_
    refine le_trans (add_le_add Finset.card_image_le Finset.card_image_le) ?_
    simpa using hcard
  have hV0 : ∀ u ∈ V, u ≠ 0 := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h <;> obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp h
    · exact hx _
    · exact hy _
  -- fibre counts
  set cx : ℂ → ℂ := fun u => ((Finset.univ.filter fun i => x i = u).card : ℂ) with hcx
  set cy : ℂ → ℂ := fun u => ((Finset.univ.filter fun j => y j = u).card : ℂ) with hcy
  have hfib : ∀ m : ℤ, ∑ i, x i ^ m = ∑ u ∈ V, cx u * u ^ m := by
    intro m
    rw [← Finset.sum_fiberwise_of_maps_to (g := x) (t := V)
      (fun i _ => Finset.mem_union_left _ (Finset.mem_image_of_mem x (Finset.mem_univ i)))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2], Finset.sum_const,
      nsmul_eq_mul]
  have hfib' : ∀ m : ℤ, ∑ j, y j ^ m = ∑ u ∈ V, cy u * u ^ m := by
    intro m
    rw [← Finset.sum_fiberwise_of_maps_to (g := y) (t := V)
      (fun j _ => Finset.mem_union_right _ (Finset.mem_image_of_mem y (Finset.mem_univ j)))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2], Finset.sum_const,
      nsmul_eq_mul]
  -- the shifted signed weights have vanishing moments `0, …, 2N`
  have hmom : ∀ k : ℕ, k < Fintype.card V →
      ∑ u : V, ((cx u - cy u) * (u : ℂ) ^ (-(N : ℤ))) * (u : ℂ) ^ k = 0 := by
    intro k hk
    have hk' : k ≤ 2 * N := by rw [Fintype.card_coe] at hk; omega
    have h1 := hM ((k : ℤ) - N) (abs_le.mpr ⟨by omega, by omega⟩)
    rw [hfib, hfib', ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    rw [Finset.sum_coe_sort V (fun u => ((cx u - cy u) * u ^ (-(N : ℤ))) * u ^ k)]
    rw [← h1]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← zpow_natCast, mul_assoc, ← zpow_add₀ (hV0 u hu),
      show -(N : ℤ) + (k : ℤ) = (k : ℤ) - N by ring]
    ring
  by_cases hv : v ∈ V
  · have h0 := eq_zero_of_moments_eq_zero (fun u : V => (u : ℂ)) Subtype.val_injective _ hmom
      ⟨v, hv⟩
    simp only at h0
    have hpow : (v : ℂ) ^ (-(N : ℤ)) ≠ 0 := zpow_ne_zero _ (hV0 v hv)
    have h1 := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hpow)
    simp only [hcx, hcy] at h1
    exact_mod_cast h1
  · have hxv : (Finset.univ.filter fun i => x i = v) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun i _ hi => hv ?_
      exact Finset.mem_union_left _ (hi ▸ Finset.mem_image_of_mem x (Finset.mem_univ i))
    have hyv : (Finset.univ.filter fun j => y j = v) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun j _ hj => hv ?_
      exact Finset.mem_union_right _ (hj ▸ Finset.mem_image_of_mem y (Finset.mem_univ j))
    simp [hxv, hyv]

/-! ### The nodes of a periodic off-line pattern -/

/-- The outer node `λ_r = e^{d_rℓ + 2πiθ_r}`. -/
def outerNode (ℓ : ℝ) {P : ℕ} (θ d : Fin P → ℝ) (r : Fin P) : ℂ :=
  cexp ((d r * ℓ : ℝ) + 2 * π * I * θ r)

/-- The inner node `μ_r = e^{−d_rℓ + 2πiθ_r}`. -/
def innerNode (ℓ : ℝ) {P : ℕ} (θ d : Fin P → ℝ) (r : Fin P) : ℂ :=
  cexp ((-(d r * ℓ) : ℝ) + 2 * π * I * θ r)

theorem norm_outerNode (ℓ : ℝ) {P : ℕ} (θ d : Fin P → ℝ) (r : Fin P) :
    ‖outerNode ℓ θ d r‖ = Real.exp (d r * ℓ) := by
  rw [outerNode, Complex.norm_exp]
  simp

theorem norm_innerNode (ℓ : ℝ) {P : ℕ} (θ d : Fin P → ℝ) (r : Fin P) :
    ‖innerNode ℓ θ d r‖ = Real.exp (-(d r * ℓ)) := by
  rw [innerNode, Complex.norm_exp]
  simp

/-- **Pattern symbols are two-sided exponential moments.**
`D(m) = Σ_r (λ_r^m + μ_r^m)` for every integer `m`. -/
theorem patternSymbol_eq_nodes {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (θ d : Fin P → ℝ) (m : ℤ) :
    patternSymbol ℓ (scaledOffset ℓ θ) d m =
      ∑ r, (outerNode ℓ θ d r ^ m + innerNode ℓ θ d r ^ m) := by
  refine Finset.sum_congr rfl fun r _ => ?_
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hc : ((2 * Real.cosh (d r * (m * ℓ)) : ℝ) : ℂ) =
      cexp ((d r * (m * ℓ) : ℝ) : ℂ) + cexp (-((d r * (m * ℓ) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cosh, Complex.cosh]
    push_cast
    ring
  rw [hc, add_mul, ← Complex.exp_add, ← Complex.exp_add, outerNode, innerNode,
    ← Complex.exp_int_mul, ← Complex.exp_int_mul, scaledOffset]
  congr 1 <;> congr 1 <;> push_cast <;> field_simp

/-- **Depth tomography at twice the Nyquist aperture.** If two periodic off-line patterns at scale
`ℓ`, with `P` and `P'` pairs per period, agree on every test of an aperture `a` with
`⌈2a/ℓ⌉ ≥ P + P' + 1`, every pair `(d_r, θ_r)` of the first occurs in the second: some `r'` has
`d'_{r'} = d_r` and the same ordinate class. -/
theorem depthTomography {ℓ : ℝ} (hℓ : 0 < ℓ) {P P' : ℕ} (θ d : Fin P → ℝ) (θ' d' : Fin P' → ℝ)
    (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2) (hd0' : ∀ r, 0 < d' r)
    (hd1' : ∀ r, d' r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hθ' : ∀ r r' : Fin P', ∀ j j' : ℤ, θ' r + j = θ' r' + j' → r = r' ∧ j = j')
    {a : ℝ} (ha : 0 < a) (hn : P + P' + 1 ≤ ⌈2 * a / ℓ⌉₊)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      (patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1).W f f =
        (patternConfig hℓ (scaledOffset ℓ θ') d' hd0' hd1').W f f) (r : Fin P) :
    ∃ r' : Fin P', d' r' = d r ∧ phasePoint θ' r' = phasePoint θ r := by
  classical
  -- equal symbols on `|m| ≤ P + P'`
  have hsym : ∀ m : ℤ, |m| ≤ (P + P' : ℕ) →
      patternSymbol ℓ (scaledOffset ℓ θ) d m = patternSymbol ℓ (scaledOffset ℓ θ') d' m := by
    intro m hm
    refine symbol_eq_of_weil_eq _ _ hℓ (patternSymbol_neg ℓ _ d) (patternSymbol_neg ℓ _ d') ha
      (fun _ hf hfs => W_patternConfig hℓ _ d hd0 hd1 (scaledOffset_injective hℓ hθ) hf
        (hasCompactSupport_of_tsupport_subset_Icc hfs))
      (fun _ hf hfs => W_patternConfig hℓ _ d' hd0' hd1' (scaledOffset_injective hℓ hθ') hf
        (hasCompactSupport_of_tsupport_subset_Icc hfs)) h ?_
    have : (|m| : ℤ) < ⌈2 * a / ℓ⌉₊ := by
      have h1 : ((P + P' : ℕ) : ℤ) < ⌈2 * a / ℓ⌉₊ := by exact_mod_cast (by omega)
      exact lt_of_le_of_lt hm h1
    exact this
  -- the node families
  set x : Fin P ⊕ Fin P → ℂ := Sum.elim (outerNode ℓ θ d) (innerNode ℓ θ d) with hx
  set y : Fin P' ⊕ Fin P' → ℂ := Sum.elim (outerNode ℓ θ' d') (innerNode ℓ θ' d') with hy
  have hx0 : ∀ i, x i ≠ 0 := by rintro (i | i) <;> exact Complex.exp_ne_zero _
  have hy0 : ∀ j, y j ≠ 0 := by rintro (j | j) <;> exact Complex.exp_ne_zero _
  have hM : ∀ m : ℤ, |m| ≤ (P + P' : ℕ) → ∑ i, x i ^ m = ∑ j, y j ^ m := by
    intro m hm
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    simp only [hx, hy, Sum.elim_inl, Sum.elim_inr]
    rw [← patternSymbol_eq_nodes hℓ, ← patternSymbol_eq_nodes hℓ]
    exact hsym m hm
  have hcard : Fintype.card (Fin P ⊕ Fin P) + Fintype.card (Fin P' ⊕ Fin P') ≤
      2 * (P + P') + 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hfib := card_fiber_eq_of_moments_eq x y hx0 hy0 hcard hM (outerNode ℓ θ d r)
  -- the outer node of `r` occurs in `y`
  have hpos : 0 < (Finset.univ.filter fun i => x i = outerNode ℓ θ d r).card :=
    Finset.card_pos.mpr ⟨Sum.inl r, by simp [hx]⟩
  rw [hfib] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hj
  have hgt : 1 < ‖outerNode ℓ θ d r‖ := by
    rw [norm_outerNode]
    have := Real.add_one_le_exp (d r * ℓ)
    nlinarith [mul_pos (hd0 r) hℓ]
  rcases j with r' | r'
  · -- an outer node: equal moduli give equal depths, equal phases give the ordinate class
    have he : outerNode ℓ θ' d' r' = outerNode ℓ θ d r := by simpa [hy] using hj.2
    refine ⟨r', ?_, ?_⟩
    · have hn := congrArg norm he
      rw [norm_outerNode, norm_outerNode] at hn
      have := Real.exp_injective hn
      exact mul_right_cancel₀ hℓ.ne' this
    · have hn := congrArg norm he
      rw [norm_outerNode, norm_outerNode] at hn
      have hdl : (d' r' * ℓ : ℝ) = d r * ℓ := Real.exp_injective hn
      rw [outerNode, outerNode, Complex.exp_add, Complex.exp_add, hdl] at he
      have hne : cexp ((d r * ℓ : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
      rw [phasePoint, phasePoint]
      exact mul_left_cancel₀ hne he
  · -- an inner node has modulus `< 1`
    have he : innerNode ℓ θ' d' r' = outerNode ℓ θ d r := by simpa [hy] using hj.2
    have hlt : ‖innerNode ℓ θ' d' r'‖ < 1 := by
      rw [norm_innerNode, ← Real.exp_zero]
      have := mul_pos (hd0' r') hℓ
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [he] at hlt
    linarith

/-! ### Below the Nyquist aperture the depth of a crystal is unreadable -/

/-- **Depth is unreadable below Nyquist.** Uniform crystals with the same phases and any two depths
have the same Weil form on every test of aperture `a ≤ Pℓ/2`. -/
theorem crystal_weil_eq_below_nyquist {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P) (θ : Fin P → ℝ)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hcr : ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k) {δ δ' : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hδ0' : 0 < δ') (hδ1' : δ' ≤ 1 / 2) {a : ℝ} (haP : a ≤ P * ℓ / 2) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    (patternConfig hℓ (scaledOffset ℓ θ) (fun _ => δ) (fun _ => hδ0) (fun _ => hδ1)).W f f =
      (patternConfig hℓ (scaledOffset ℓ θ) (fun _ => δ') (fun _ => hδ0') (fun _ => hδ1')).W f f := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  rw [W_patternConfig hℓ _ _ _ _ (scaledOffset_injective hℓ hθ) hf hfc,
    W_patternConfig hℓ _ _ _ _ (scaledOffset_injective hℓ hθ) hf hfc]
  congr 1
  refine tsum_congr fun m => ?_
  -- either the kernel vanishes or both modes vanish
  by_cases hm0 : m = 0
  · subst hm0
    rw [patternSymbol_zero, patternSymbol_zero]
  by_cases hmP : |m| < P
  · have hmode : ∀ (e : ℝ), patternSymbol ℓ (scaledOffset ℓ θ) (fun _ => e) m = 0 := by
      intro e
      obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
      · rw [patternSymbol_uniform hℓ, powerSum_eq_zero_of_pow_eq _ (phasePoint_injective hθ)
          (fun i => phasePoint_pow_eq_of_crystal θ hcr i ⟨0, hP⟩) (by omega)
          (by rw [abs_of_nonneg (by positivity)] at hmP; exact_mod_cast hmP), mul_zero]
      · rw [patternSymbol_neg, patternSymbol_uniform hℓ,
          powerSum_eq_zero_of_pow_eq _ (phasePoint_injective hθ)
          (fun i => phasePoint_pow_eq_of_crystal θ hcr i ⟨0, hP⟩) (by omega)
          (by rw [abs_neg, abs_of_nonneg (by positivity)] at hmP; exact_mod_cast hmP), mul_zero,
          map_zero]
    rw [hmode, hmode]
  · push Not at hmP
    rw [weilTest_eq_zero_of_two_mul_le hf.continuous hfs, zero_mul, zero_mul]
    rw [abs_mul, abs_of_pos hℓ]
    have : (P : ℝ) ≤ |(m : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hmP
    nlinarith

end GaloisForLFunctions.SquareRootThreshold
