import GaloisForLFunctions.ZeroForcingCalculus.SingleQuartetRationalRaysAndDilationPoles

/-!
# Half-Quartet Dilation Pole Isolation, Shifted Nonvanishing, and Eisenstein Scattering Duals

Under a single off-line zero quartet `Q(ρ₀) = {ρ₀, conj ρ₀, 1 - ρ₀, 1 - conj ρ₀}`
(`HasSingleOffLineQuartet ρ₀`), this module establishes three exact structural consequences for
affine-dilated zeta values, the `k`-dilated Euler quotients `((s - 1) ζ(s))^m / ζ(k s)`
(`dilatedPowerQuotient k m`), and the `SL₂(ℤ)` Eisenstein scattering parameters `2 w - 1 ∈ Q(ρ₀)`:

1. **Affine-reflected and integer-shifted nonvanishing**
   (`riemannZeta_one_sub_div_nat_ne_zero_of_singleQuartet`,
   `riemannZeta_shift_div_nat_ne_zero_of_singleQuartet`,
   `riemannZeta_two_sub_and_sub_one_ne_zero_of_singleQuartet`):
   For every `k ≥ 2` and `ρ ∈ zeroQuartetSet ρ₀`, both `1 - ρ / k` and `((k - 1) + ρ) / k` lie in
   `{1/2 < Re s < 1}` with ordinate `|Im| = |Im ρ₀| / k < |Im ρ₀|`, so `ζ` cannot vanish at either
   point. Moreover, `ζ(2 - ρ) ≠ 0` (`Re(2 - ρ) > 1`) and `ζ(ρ - 1) ≠ 0` (by `ξ`-reflection and
   `Im(ρ - 1) ≠ 0`).

2. **Exact `{Re s > 1 / (2k)}` half-quartet pole isolation of `dilatedPowerQuotient k m`**
   (`meromorphicOrderAt_riemannZeta_eq_of_mem_zeroQuartetSet`,
   `dilatedPowerQuotient_rightHalf_poles_eq_of_singleQuartet`,
   `dilatedPowerQuotient_leftHalf_poles_of_singleQuartet`,
   `squarefreeDilationQuotient_quarter_pole_isolation`):
   Under `HasSingleOffLineQuartet ρ₀`, for every `k ≥ 2` and `m : ℕ`, the pole set of
   `((s - 1) ζ(s))^m / ζ(k s)` in `{Re s > 1 / (2k)}` is **precisely** the two-point conjugate pair
   `{ρ₀ / k, conj ρ₀ / k}`, each of exact meromorphic order `- ord_{ρ₀} ζ < 0`, while the reflected
   pair `{(1 - ρ₀) / k, (1 - conj ρ₀) / k}` is strictly separated into `{0 < Re s < 1 / (2k)}` with
   the same pole order. At `k = 2, m = 1`, `(s - 1) ζ(s) / ζ(2s)` isolates `{ρ₀ / 2, conj ρ₀ / 2}`
   inside `{1/4 < Re s < 1/2}`.

3. **Eisenstein zero-scattering dual modes across the `3/4` threshold**
   (`eisensteinDualMinus`, `eisensteinDualPlus`, `eisensteinDualModes_scattering_and_spectral_split`):
   The two Eisenstein scattering roots `w_- = 1 - ρ₀ / 2` and `w_+ = (1 + ρ₀) / 2` solving
   `2 w_- - 1 = 1 - ρ₀` and `2 w_+ - 1 = ρ₀` are strictly separated across `Re w = 3/4`
   (`1/2 < Re w_- < 3/4 < Re w_+ < 1`), satisfy `ξ(2 w_± - 1) = 0`, `ξ(2 w_±) ≠ 0`, and
   `ζ(w_±) ≠ 0`, and carry distinct non-real hyperbolic Laplace eigenvalues `w_± (1 - w_±)` split
   by `(2 ρ₀ - 1) / 4 ≠ 0`.
-/

noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology Zeta23
open scoped ComplexConjugate
open GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GaloisForLFunctions.ZeroForcingCalculus

/-! ## 1. Common zeta multiplicity across `zeroQuartetSet ρ₀` -/

private theorem div_nat_re (z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (z / (k : ℂ)).re = z.re / (k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm := congrArg Complex.re
    (show ((k : ℝ) : ℂ) * (z / (k : ℂ)) = z by push_cast; exact mul_div_cancel₀ z hkc_ne)
  rw [Complex.re_ofReal_mul] at hm
  exact (eq_div_iff hk_pos.ne').mpr ((mul_comm _ _).trans hm)

private theorem div_nat_im (z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (z / (k : ℂ)).im = z.im / (k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm := congrArg Complex.im
    (show ((k : ℝ) : ℂ) * (z / (k : ℂ)) = z by push_cast; exact mul_div_cancel₀ z hkc_ne)
  rw [Complex.im_ofReal_mul] at hm
  exact (eq_div_iff hk_pos.ne').mpr ((mul_comm _ _).trans hm)

/-- On the open critical strip `0 < Re ρ < 1`, `meromorphicOrderAt riemannZeta ρ` agrees with
`meromorphicOrderAt RHTower.xi ρ` and equals `(quartetCopyMult ρ : ℤ)`. -/
theorem meromorphicOrderAt_riemannZeta_eq_quartetCopyMult {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hζ : riemannZeta ρ = 0) :
    meromorphicOrderAt riemannZeta ρ = ((quartetCopyMult ρ : ℤ) : WithTop ℤ) := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  set g : ℂ → ℂ := fun s => s * (s - 1) / 2 * Complex.Gammaℝ s
  have hΓ : AnalyticAt ℂ Complex.Gammaℝ ρ := GaloisForLFunctions.HTGeometry.analyticAt_Gammaℝ h0
  have hg : AnalyticAt ℂ g ρ :=
    ((((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div analyticAt_const two_ne_zero)).mul hΓ)
  have hg0 : g ρ ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)) two_ne_zero)
      (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  have hxi_ord : meromorphicOrderAt RHTower.xi ρ = meromorphicOrderAt riemannZeta ρ := by
    rw [← meromorphicOrderAt_mul_of_ne_zero (f := riemannZeta) hg hg0]
    refine meromorphicOrderAt_congr ?_
    have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds ⟨h0, hρ1⟩)] with s hs
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs.1
    rw [RHTower.xi_eq_half_mul hs0 hs.2, Pi.mul_apply, riemannZeta_def_of_ne_zero hs0]
    dsimp [g]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs.1]
  have hntop : meromorphicOrderAt RHTower.xi ρ ≠ ⊤ := by
    rw [hxi_ord]
    exact meromorphicOrderAt_riemannZeta_ne_top ρ
  have hpos : 0 < meromorphicOrderAt RHTower.xi ρ := by
    rw [hxi_ord]
    exact meromorphicOrderAt_pos_of_analyticAt_eq_zero (analyticAt_riemannZeta hρ1) hζ
  lift meromorphicOrderAt RHTower.xi ρ to ℤ using hntop with n hn
  have hn_pos : 0 < n := by exact_mod_cast hpos
  have hdiv : (MeromorphicOn.divisor RHTower.xi Set.univ) ρ = n := by
    rw [MeromorphicOn.divisor_apply (RHTower.xi_analyticOnNhd_univ.meromorphicOn) (Set.mem_univ ρ),
      ← hn, WithTop.untop₀_coe]
  rw [← hxi_ord]
  unfold quartetCopyMult
  rw [hdiv, Int.toNat_of_nonneg hn_pos.le]

/-- Every member of `zeroQuartetSet ρ₀` carries the same zeta vanishing order as `ρ₀`. -/
theorem meromorphicOrderAt_riemannZeta_eq_of_mem_zeroQuartetSet {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ ∈ zeroQuartetSet ρ₀) :
    meromorphicOrderAt riemannZeta ρ = meromorphicOrderAt riemannZeta ρ₀ := by
  obtain ⟨hζ, h0, h1, -, -⟩ := mem_zeroQuartetSet_invariants hq hρ
  obtain ⟨hζ₀, h0₀, h1₀⟩ := hq.2.1
  rw [meromorphicOrderAt_riemannZeta_eq_quartetCopyMult h0 h1 hζ,
    meromorphicOrderAt_riemannZeta_eq_quartetCopyMult h0₀ h1₀ hζ₀]
  congr 2
  simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · rfl
  · exact quartetCopyMult_conj ρ₀
  · exact quartetCopyMult_one_sub ρ₀
  · exact quartetCopyMult_one_sub_conj ρ₀

/-! ## 2. Affine-reflected and integer-shifted nonvanishing under a single quartet -/

/-- **Affine-reflected dilation nonvanishing (`1 - ρ / k`).** Under `HasSingleOffLineQuartet ρ₀`,
for every `k ≥ 2` and `ρ ∈ zeroQuartetSet ρ₀`, `1 - ρ / k` lies strictly in `{1/2 < Re s < 1}` with
`|Im(1 - ρ / k)| = |Im ρ₀| / k < |Im ρ₀|`, so `riemannZeta (1 - ρ / k) ≠ 0`. -/
theorem riemannZeta_one_sub_div_nat_ne_zero_of_singleQuartet {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ ∈ zeroQuartetSet ρ₀) {k : ℕ} (hk : 2 ≤ k) :
    riemannZeta (1 - ρ / (k : ℂ)) ≠ 0 := by
  intro hζ
  have hk1 : 1 ≤ k := by omega
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  obtain ⟨-, h0, h1, him_eq, -⟩ := mem_zeroQuartetSet_invariants hq hρ
  set w : ℂ := 1 - ρ / (k : ℂ)
  have hw_re : w.re = 1 - ρ.re / (k : ℝ) := by
    simp [w, div_nat_re ρ hk1]
  have hw_im : w.im = -(ρ.im / (k : ℝ)) := by
    simp [w, div_nat_im ρ hk1]
  have hdiv_lt_half : ρ.re / (k : ℝ) < 1 / 2 := by
    rw [div_lt_div_iff₀ hk_pos (by norm_num)]
    nlinarith
  have hdiv_pos : 0 < ρ.re / (k : ℝ) := div_pos h0 hk_pos
  have hw_gt_half : 1 / 2 < w.re := by linarith
  have hw_lt1 : w.re < 1 := by linarith
  have hw_mem : w ∈ zeroQuartetSet ρ₀ := by
    rw [← hq.2.2]
    exact ⟨⟨hζ, by linarith, hw_lt1⟩, ne_of_gt hw_gt_half⟩
  have hw_im_eq : |w.im| = |ρ₀.im| := (mem_zeroQuartetSet_invariants hq hw_mem).2.2.2.1
  rw [hw_im, abs_neg, abs_div, abs_of_pos hk_pos, him_eq] at hw_im_eq
  have him_pos : 0 < |ρ₀.im| := by linarith [hq.four_lt_abs_im]
  have hmul : |ρ₀.im| = |ρ₀.im| * (k : ℝ) := (div_eq_iff hk_pos.ne').mp hw_im_eq
  nlinarith

/-- **Affine-convex dilation nonvanishing (`((k - 1) + ρ) / k`).** Under
`HasSingleOffLineQuartet ρ₀`, for every `k ≥ 2` and `ρ ∈ zeroQuartetSet ρ₀`,
`riemannZeta (((k - 1) + ρ) / k) ≠ 0`. -/
theorem riemannZeta_shift_div_nat_ne_zero_of_singleQuartet {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ ∈ zeroQuartetSet ρ₀) {k : ℕ} (hk : 2 ≤ k) :
    riemannZeta ((((k - 1 : ℕ) : ℂ) + ρ) / (k : ℂ)) ≠ 0 := by
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1_sub : 1 - ρ ∈ zeroQuartetSet ρ₀ := by
    simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ ⊢
    rcases hρ with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · left; ring
    · right; left; ring
  have heq : (((k - 1 : ℕ) : ℂ) + ρ) / (k : ℂ) = 1 - (1 - ρ) / (k : ℂ) := by
    have hk_sub : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hk_sub]
    field_simp [hkc_ne]
    ring
  rw [heq]
  exact riemannZeta_one_sub_div_nat_ne_zero_of_singleQuartet hq h1_sub hk

/-- **Integer-step nonvanishing (`2 - ρ` and `ρ - 1`).** For every strip zero `ρ` with
`0 < Re ρ < 1` and `Im ρ ≠ 0` (in particular every `ρ ∈ zeroQuartetSet ρ₀` under
`HasSingleOffLineQuartet ρ₀`), both `riemannZeta (2 - ρ) ≠ 0` and `riemannZeta (ρ - 1) ≠ 0`. -/
theorem riemannZeta_two_sub_and_sub_one_ne_zero_of_strip {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) :
    riemannZeta (2 - ρ) ≠ 0 ∧ riemannZeta (ρ - 1) ≠ 0 := by
  have h2_re : 1 < (2 - ρ).re := by simp; linarith
  have h2_nz : riemannZeta (2 - ρ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h2_re.le
  refine ⟨h2_nz, fun hsub_zero => ?_⟩
  have hnot_triv : ¬ ∃ n : ℕ, ρ - 1 = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp at this
    exact him this
  have hsub_ne1 : ρ - 1 ≠ 1 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact him this
  have hxi_sub : RHTower.xi (ρ - 1) = 0 :=
    RHTower.xi_eq_zero_of_zeta_eq_zero hsub_zero hnot_triv hsub_ne1
  have hxi_two : RHTower.xi (2 - ρ) = 0 := by
    have hrefl := RHTower.xi_one_sub (2 - ρ)
    rw [show (1 : ℂ) - (2 - ρ) = ρ - 1 by ring] at hrefl
    exact hrefl.symm.trans hxi_sub
  have h2_ne1 : (2 : ℂ) - ρ ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  exact h2_nz ((RHTower.xi_eq_zero_iff (by linarith) h2_ne1).mp hxi_two)

/-- Under `HasSingleOffLineQuartet ρ₀`, `riemannZeta (2 - ρ) ≠ 0` and `riemannZeta (ρ - 1) ≠ 0`
hold for every `ρ ∈ zeroQuartetSet ρ₀`. -/
theorem riemannZeta_two_sub_and_sub_one_ne_zero_of_singleQuartet {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ ∈ zeroQuartetSet ρ₀) :
    riemannZeta (2 - ρ) ≠ 0 ∧ riemannZeta (ρ - 1) ≠ 0 := by
  obtain ⟨-, h0, h1, him_eq, -⟩ := mem_zeroQuartetSet_invariants hq hρ
  have him : ρ.im ≠ 0 := by
    intro h0_im
    rw [h0_im, abs_zero] at him_eq
    linarith [hq.four_lt_abs_im]
  exact riemannZeta_two_sub_and_sub_one_ne_zero_of_strip h0 h1 him

/-! ## 3. Exact half-quartet pole isolation of `dilatedPowerQuotient k m` -/

/-- **Exact `{Re s > 1 / (2k)}` half-quartet pole isolation.** Under `HasSingleOffLineQuartet ρ₀`,
for every `k ≥ 2` and `m : ℕ`:
1. `ρ₀ / k` and `conj ρ₀ / k` are distinct points in `{1 / (2k) < Re s < 1 / k}`;
2. The set of poles (`meromorphicOrderAt < 0`) of `dilatedPowerQuotient k m` in
   `{Re s > 1 / (2k)}` is **exactly** `{ρ₀ / k, conj ρ₀ / k}`;
3. Both poles have exact meromorphic order `- meromorphicOrderAt riemannZeta ρ₀ < 0`. -/
theorem dilatedPowerQuotient_rightHalf_poles_eq_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    ρ₀ / (k : ℂ) ≠ conj ρ₀ / (k : ℂ) ∧
      {s : ℂ | 1 / (2 * (k : ℝ)) < s.re ∧ meromorphicOrderAt (dilatedPowerQuotient k m) s < 0} =
        {ρ₀ / (k : ℂ), conj ρ₀ / (k : ℂ)} ∧
      meromorphicOrderAt (dilatedPowerQuotient k m) (ρ₀ / (k : ℂ)) =
        - meromorphicOrderAt riemannZeta ρ₀ ∧
      meromorphicOrderAt (dilatedPowerQuotient k m) (conj ρ₀ / (k : ℂ)) =
        - meromorphicOrderAt riemannZeta ρ₀ := by
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmem₀ : ρ₀ ∈ zeroQuartetSet ρ₀ := Or.inl rfl
  have hmem_c : conj ρ₀ ∈ zeroQuartetSet ρ₀ := Or.inr (Or.inl rfl)
  have hne_pair : ρ₀ / (k : ℂ) ≠ conj ρ₀ / (k : ℂ) := by
    intro heq
    have hρ_eq : ρ₀ = conj ρ₀ := by
      have hm := congrArg ((k : ℂ) * ·) heq
      simpa [mul_div_cancel₀ _ hkc_ne] using hm
    have him := congrArg Complex.im hρ_eq
    simp at him
    exact hq.im_ne_zero (by linarith)
  have hord₀ := dilatedPowerQuotient_neg_order_of_singleQuartet hq hmem₀ hk m
  have hord_c := dilatedPowerQuotient_neg_order_of_singleQuartet hq hmem_c hk m
  have hord_c_eq : meromorphicOrderAt (dilatedPowerQuotient k m) (conj ρ₀ / (k : ℂ)) =
      - meromorphicOrderAt riemannZeta ρ₀ := by
    rw [hord_c.1, meromorphicOrderAt_riemannZeta_eq_of_mem_zeroQuartetSet hq hmem_c]
  refine ⟨hne_pair, ?_, hord₀.1, hord_c_eq⟩
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hs_re, hs_neg⟩
    -- If `ζ(k s) ≠ 0` or `k s = 1`, `dilatedPowerQuotient k m` is analytic at `s`, contradiction.
    have hks_re : 1 / 2 < ((k : ℂ) * s).re := by
      have hm : ((k : ℂ) * s).re = (k : ℝ) * s.re := by simp
      have hgt : 1 / 2 < s.re * (k : ℝ) := by
        have := (div_lt_iff₀ hk_pos).mp (show (1 / 2) / (k : ℝ) < s.re by
          rwa [div_div] )
        exact this
      linarith
    by_contra hnot
    push Not at hnot
    have hden_ne : RHTower.zetaResidueUnit ((k : ℂ) * s) ≠ 0 := by
      by_cases hks1 : (k : ℂ) * s = 1
      · rw [hks1, RHTower.zetaResidueUnit_one]
        exact one_ne_zero
      · rw [RHTower.zetaResidueUnit, Function.update_of_ne hks1]
        refine mul_ne_zero (sub_ne_zero.mpr hks1) fun hζk => ?_
        have hks_lt1 : ((k : ℂ) * s).re < 1 := by
          by_contra hge
          exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζk
        have hks_mem : (k : ℂ) * s ∈ zeroQuartetSet ρ₀ := by
          rw [← hq.2.2]
          exact ⟨⟨hζk, by linarith, hks_lt1⟩, ne_of_gt hks_re⟩
        simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hks_mem
        rcases hks_mem with h1 | h2 | h3 | h4
        · exact hnot.1 ((eq_div_iff hkc_ne).mpr ((mul_comm _ _).trans h1))
        · exact hnot.2 ((eq_div_iff hkc_ne).mpr ((mul_comm _ _).trans h2))
        · rw [h3] at hks_re; simp at hks_re; linarith [hq.1]
        · rw [h4] at hks_re; simp at hks_re; linarith [hq.1]
    have han : AnalyticAt ℂ
        (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1) /
          RHTower.zetaResidueUnit ((k : ℂ) * w)) s := by
      have hnum : AnalyticAt ℂ
          (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1)) s :=
        ((RHTower.analyticAt_zetaResidueUnit s).pow m).mul
          ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
      have hden : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit ((k : ℂ) * w)) s :=
        (RHTower.analyticAt_zetaResidueUnit ((k : ℂ) * s)).comp (analyticAt_const.mul analyticAt_id)
      exact hnum.div hden hden_ne
    rw [meromorphicOrderAt_congr (dilatedPowerQuotient_eventuallyEq_unit hk1 m s)] at hs_neg
    exact not_le.mpr hs_neg han.meromorphicOrderAt_nonneg
  · rintro (rfl | rfl)
    · refine ⟨?_, hord₀.2⟩
      rw [div_nat_re ρ₀ hk1, ← div_div]
      exact div_lt_div_of_pos_right hq.1 hk_pos
    · refine ⟨?_, hord_c.2⟩
      rw [div_nat_re (conj ρ₀) hk1, Complex.conj_re, ← div_div]
      exact div_lt_div_of_pos_right hq.1 hk_pos

/-- **Reflected left-pair poles in `{0 < Re s < 1 / (2k)}`.** Under `HasSingleOffLineQuartet ρ₀`,
for every `k ≥ 2` and `m : ℕ`, the reflected points `(1 - ρ₀) / k` and `(1 - conj ρ₀) / k` are
distinct, lie strictly in `0 < Re s < 1 / (2k)`, and carry poles of exact order
`- meromorphicOrderAt riemannZeta ρ₀ < 0`. -/
theorem dilatedPowerQuotient_leftHalf_poles_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (1 - ρ₀) / (k : ℂ) ≠ (1 - conj ρ₀) / (k : ℂ) ∧
      0 < ((1 - ρ₀) / (k : ℂ)).re ∧ ((1 - ρ₀) / (k : ℂ)).re < 1 / (2 * (k : ℝ)) ∧
      0 < ((1 - conj ρ₀) / (k : ℂ)).re ∧ ((1 - conj ρ₀) / (k : ℂ)).re < 1 / (2 * (k : ℝ)) ∧
      meromorphicOrderAt (dilatedPowerQuotient k m) ((1 - ρ₀) / (k : ℂ)) =
        - meromorphicOrderAt riemannZeta ρ₀ ∧
      meromorphicOrderAt (dilatedPowerQuotient k m) ((1 - conj ρ₀) / (k : ℂ)) =
        - meromorphicOrderAt riemannZeta ρ₀ := by
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmem_r : 1 - ρ₀ ∈ zeroQuartetSet ρ₀ := Or.inr (Or.inr (Or.inl rfl))
  have hmem_rc : 1 - conj ρ₀ ∈ zeroQuartetSet ρ₀ := Or.inr (Or.inr (Or.inr rfl))
  have hne : (1 - ρ₀) / (k : ℂ) ≠ (1 - conj ρ₀) / (k : ℂ) := by
    intro heq
    have hm := congrArg ((k : ℂ) * ·) heq
    simp only [mul_div_cancel₀ _ hkc_ne] at hm
    have him := congrArg Complex.im hm
    simp at him
    exact hq.im_ne_zero (by linarith)
  have hre_r : ((1 - ρ₀) / (k : ℂ)).re = (1 - ρ₀.re) / (k : ℝ) := by
    rw [div_nat_re _ hk1]; simp
  have hre_rc : ((1 - conj ρ₀) / (k : ℂ)).re = (1 - ρ₀.re) / (k : ℝ) := by
    rw [div_nat_re _ hk1]; simp
  have hpos : 0 < (1 - ρ₀.re) / (k : ℝ) := div_pos (by linarith [hq.re_lt_one]) hk_pos
  have hlt : (1 - ρ₀.re) / (k : ℝ) < 1 / (2 * (k : ℝ)) := by
    rw [← div_div]
    exact div_lt_div_of_pos_right (by linarith [hq.1]) hk_pos
  have hord_r := (dilatedPowerQuotient_neg_order_of_singleQuartet hq hmem_r hk m).1
  have hord_rc := (dilatedPowerQuotient_neg_order_of_singleQuartet hq hmem_rc hk m).1
  rw [meromorphicOrderAt_riemannZeta_eq_of_mem_zeroQuartetSet hq hmem_r] at hord_r
  rw [meromorphicOrderAt_riemannZeta_eq_of_mem_zeroQuartetSet hq hmem_rc] at hord_rc
  exact ⟨hne, hre_r ▸ hpos, hre_r ▸ hlt, hre_rc ▸ hpos, hre_rc ▸ hlt, hord_r, hord_rc⟩

/-- **Squarefree Euler quotient (`k = 2, m = 1`) quarter-line pole isolation.** Under
`HasSingleOffLineQuartet ρ₀`, `(s - 1) ζ(s) / ζ(2s)` (`dilatedPowerQuotient 2 1`) has
`{ρ₀ / 2, conj ρ₀ / 2} ⊂ {1/4 < Re s < 1/2}` as its **unique** poles in `{Re s > 1/4}`, separated
across the scaled critical line `Re s = 1/4` from `{(1 - ρ₀) / 2, (1 - conj ρ₀) / 2} ⊂ {0 < Re s < 1/4}`. -/
theorem squarefreeDilationQuotient_quarter_pole_isolation {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    {s : ℂ | 1 / 4 < s.re ∧ meromorphicOrderAt (dilatedPowerQuotient 2 1) s < 0} =
        {ρ₀ / 2, conj ρ₀ / 2} ∧
      1 / 4 < (ρ₀ / 2).re ∧ (ρ₀ / 2).re < 1 / 2 ∧
      0 < ((1 - ρ₀) / 2).re ∧ ((1 - ρ₀) / 2).re < 1 / 4 := by
  obtain ⟨-, hset, -, -⟩ :=
    dilatedPowerQuotient_rightHalf_poles_eq_of_singleQuartet hq (by norm_num : 2 ≤ 2) 1
  norm_num at hset
  have hre : (ρ₀ / 2).re = ρ₀.re / 2 := by simp
  have hre_l : ((1 - ρ₀) / 2).re = (1 - ρ₀.re) / 2 := by simp
  refine ⟨hset, ?_, ?_, ?_, ?_⟩ <;> linarith [hq.1, hq.re_lt_one]

/-! ## 4. Eisenstein zero-scattering dual modes across the `3/4` threshold -/

/-- Sub-`3/4` Eisenstein scattering dual root `w_- = 1 - ρ₀ / 2` (`2 w_- - 1 = 1 - ρ₀`). -/
def eisensteinDualMinus (ρ₀ : ℂ) : ℂ := 1 - ρ₀ / 2

/-- Super-`3/4` Eisenstein scattering dual root `w_+ = (1 + ρ₀) / 2` (`2 w_+ - 1 = ρ₀`). -/
def eisensteinDualPlus (ρ₀ : ℂ) : ℂ := (1 + ρ₀) / 2

/-- **Eisenstein zero-scattering dual split under `HasSingleOffLineQuartet ρ₀`.**
1. Strict separation across `Re w = 3/4`:
   `1/2 < Re w_- < 3/4 < Re w_+ < 1`;
2. Scattering vanishing (`ξ(2 w_± - 1) = 0`) paired with denominator and Euler nonvanishing
   (`ξ(2 w_±) ≠ 0` and `ζ(w_±) ≠ 0`);
3. Distinct non-real hyperbolic Laplace eigenvalues `w_± (1 - w_±)` with exact difference
   `(2 ρ₀ - 1) / 4 ≠ 0`. -/
theorem eisensteinDualModes_scattering_and_spectral_split {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    let wMinus := eisensteinDualMinus ρ₀
    let wPlus := eisensteinDualPlus ρ₀
    1 / 2 < wMinus.re ∧ wMinus.re < 3 / 4 ∧
      3 / 4 < wPlus.re ∧ wPlus.re < 1 ∧
      RHTower.xi (2 * wMinus - 1) = 0 ∧ RHTower.xi (2 * wMinus) ≠ 0 ∧ riemannZeta wMinus ≠ 0 ∧
      RHTower.xi (2 * wPlus - 1) = 0 ∧ RHTower.xi (2 * wPlus) ≠ 0 ∧ riemannZeta wPlus ≠ 0 ∧
      (wMinus * (1 - wMinus)).im = (1 - ρ₀.re) * ρ₀.im / 2 ∧
      (wMinus * (1 - wMinus)).im ≠ 0 ∧
      (wPlus * (1 - wPlus)).im = -(ρ₀.re * ρ₀.im) / 2 ∧
      (wPlus * (1 - wPlus)).im ≠ 0 ∧
      wMinus * (1 - wMinus) - wPlus * (1 - wPlus) = (2 * ρ₀ - 1) / 4 ∧
      wMinus * (1 - wMinus) ≠ wPlus * (1 - wPlus) := by
  intro wMinus wPlus
  have hm_re : wMinus.re = 1 - ρ₀.re / 2 := by simp [wMinus, eisensteinDualMinus]
  have hp_re : wPlus.re = (1 + ρ₀.re) / 2 := by simp [wPlus, eisensteinDualPlus]
  have hmem₀ : ρ₀ ∈ zeroQuartetSet ρ₀ := Or.inl rfl
  have hm_zeta : riemannZeta wMinus ≠ 0 := by
    simpa [wMinus, eisensteinDualMinus] using
      riemannZeta_one_sub_div_nat_ne_zero_of_singleQuartet hq hmem₀ (by norm_num : 2 ≤ 2)
  have hp_zeta : riemannZeta wPlus ≠ 0 := by
    simpa [wPlus, eisensteinDualPlus] using
      riemannZeta_shift_div_nat_ne_zero_of_singleQuartet hq hmem₀ (by norm_num : 2 ≤ 2)
  have h2m_sub : 2 * wMinus - 1 = 1 - ρ₀ := by dsimp [wMinus, eisensteinDualMinus]; ring
  have h2p_sub : 2 * wPlus - 1 = ρ₀ := by dsimp [wPlus, eisensteinDualPlus]; ring
  have hxi_m0 : RHTower.xi (2 * wMinus - 1) = 0 := by
    rw [h2m_sub, RHTower.xi_one_sub]
    exact hq.xi_eq_zero
  have hxi_p0 : RHTower.xi (2 * wPlus - 1) = 0 := by
    rw [h2p_sub]
    exact hq.xi_eq_zero
  have h2m_eq : 2 * wMinus = 2 - ρ₀ := by dsimp [wMinus, eisensteinDualMinus]; ring
  have h2p_eq : 2 * wPlus = 1 + ρ₀ := by dsimp [wPlus, eisensteinDualPlus]; ring
  have hxi_m_nz : RHTower.xi (2 * wMinus) ≠ 0 := by
    rw [h2m_eq]
    have hre_gt1 : 1 < (2 - ρ₀).re := by simp; linarith [hq.re_lt_one]
    have hne1 : (2 : ℂ) - ρ₀ ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hq.re_lt_one]
    intro h0
    exact riemannZeta_ne_zero_of_one_le_re hre_gt1.le ((RHTower.xi_eq_zero_iff (by linarith) hne1).mp h0)
  have hxi_p_nz : RHTower.xi (2 * wPlus) ≠ 0 := by
    rw [h2p_eq]
    have hre_gt1 : 1 < (1 + ρ₀).re := by simp; linarith [hq.1]
    have hne1 : (1 : ℂ) + ρ₀ ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hq.1]
    intro h0
    exact riemannZeta_ne_zero_of_one_le_re hre_gt1.le ((RHTower.xi_eq_zero_iff (by linarith) hne1).mp h0)
  have heig_m : wMinus * (1 - wMinus) = (2 * ρ₀ - ρ₀ ^ 2) / 4 := by
    dsimp [wMinus, eisensteinDualMinus]; ring
  have heig_p : wPlus * (1 - wPlus) = (1 - ρ₀ ^ 2) / 4 := by
    dsimp [wPlus, eisensteinDualPlus]; ring
  have him_m : (wMinus * (1 - wMinus)).im = (1 - ρ₀.re) * ρ₀.im / 2 := by
    rw [heig_m, sq]
    simp [Complex.mul_im]
    ring
  have him_p : (wPlus * (1 - wPlus)).im = -(ρ₀.re * ρ₀.im) / 2 := by
    rw [heig_p, sq]
    simp [Complex.mul_im]
    ring
  have him_m_nz : (wMinus * (1 - wMinus)).im ≠ 0 := by
    rw [him_m]
    exact div_ne_zero (mul_ne_zero (by linarith [hq.re_lt_one]) hq.im_ne_zero) two_ne_zero
  have him_p_nz : (wPlus * (1 - wPlus)).im ≠ 0 := by
    rw [him_p]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by linarith [hq.1]) hq.im_ne_zero)) two_ne_zero
  have hdiff : wMinus * (1 - wMinus) - wPlus * (1 - wPlus) = (2 * ρ₀ - 1) / 4 := by
    rw [heig_m, heig_p]; ring
  have hdiff_nz : wMinus * (1 - wMinus) ≠ wPlus * (1 - wPlus) := by
    intro heq
    have h0 := sub_eq_zero.mpr heq
    rw [hdiff] at h0
    have hre0 := congrArg Complex.re h0
    simp at hre0
    linarith [hq.1]
  refine ⟨by linarith [hq.re_lt_one], by linarith [hq.1], by linarith [hq.1],
    by linarith [hq.re_lt_one], hxi_m0, hxi_m_nz, hm_zeta, hxi_p0, hxi_p_nz, hp_zeta,
    him_m, him_m_nz, him_p, him_p_nz, hdiff, hdiff_nz⟩

end GaloisForLFunctions.ZeroForcingCalculus
