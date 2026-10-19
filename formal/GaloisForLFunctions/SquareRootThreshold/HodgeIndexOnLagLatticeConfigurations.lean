import GaloisForLFunctions.SquareRootThreshold.CrystalRigidityAtTheSquareRootThreshold
import GaloisForLFunctions.SquareRootThreshold.DepthProfileNyquistCeiling
import GaloisForLFunctions.RHTower.LandauHeightKreinPinning
import GaloisForLFunctions.RHTower.IsolatedDeepZeroHodgeIndex

/-!
# The Hodge index on lag-lattice configurations

The level-`a` Hodge index (`RHTower.HodgeIndexAtLevel`) asks for Weil positivity only on tests
whose transforms vanish at the pole points `±i/2`. For configurations with a lag formula
`W(f, f) = ℓ Σ_m k(mℓ) D(m)` this constraint costs nothing.

* **Polar blindness** (`hodgeIndex_iff_toeplitz_of_lagFormula`,
  `hodgeIndex_iff_weil_nonneg_of_lagFormula`). The Hodge index at level `a` holds iff the Toeplitz
  form of `D` of size `⌈2a/ℓ⌉` is positive semidefinite, iff full Weil positivity holds at
  aperture `a`. The Toeplitz witness is built from translates of one bump at the lag points; the
  polar-free bump `κ'' − κ/4` (`RHTower.scaledBumpPolarFree`) has transform vanishing at `±i/2`,
  and so has every combination of its translates.
* **The lattice masks exactly to `L/2`** (`offLineLattice_hodgeIndex_iff`). The off-line lattice
  `{½ ± δ + 2πik/L}` satisfies the level-`a` Hodge index iff `a ≤ L/2`. This is the exact form of
  the masking half of `RHTower.offLineLattice_masks_at_linear_level`.
* **Profiles** (`profileConfig_not_hodgeIndex_of_nyquist_lt`): a periodic depth profile with an
  off-line residue violates the Hodge index at every level `a > L/2`.
* **Crystal rigidity for the Hodge index** (`hodgeIndex_frequently_iff_uniform_crystal`). A
  periodic off-line pattern of fixed shape satisfies the Hodge index at some level
  `a > (P−1)ℓ/2` at unboundedly many scales iff it is a uniform crystal; every other shape violates
  it at all such levels for all large scales (`exists_hodge_violation_of_not_uniform_crystal`).
* **Jitter** (`jitterConfig_hodgeIndex_iff`): the jittered lattice satisfies the Hodge index on
  `L/4 < a ≤ L/2` iff `cosh(δL/2)|sin(εL/2)| ≤ 1`.

So the linear-level masking used in `RHTower.not_forall_hodge_exclusion_sublinear_level` is a
crystalline phenomenon: among periodic off-line patterns of fixed shape only the uniform crystal
masks up to the square-root threshold.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower Bottcher

/-! ### Lag-point tests built from one bump -/

/-- The lag-point test `Σ_i c_i β(t − p_i)` with `p_i = (i − (n−1)/2)ℓ`. -/
def bumpTest (β : ℝ → ℂ) (ℓ : ℝ) {n : ℕ} (c : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∑ i : Fin n, c i * β (t - lagPoint n ℓ i)

theorem contDiff_bumpTest {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) (ℓ : ℝ) {n : ℕ} (c : Fin n → ℂ) :
    ContDiff ℝ 2 (bumpTest β ℓ c) := by
  unfold bumpTest
  exact ContDiff.sum fun i _ => contDiff_const.mul (hβ.comp (contDiff_id.sub contDiff_const))

theorem tsupport_bumpTest_subset {β : ℝ → ℂ} {w : ℝ} (hβs : ∀ x, β x ≠ 0 → |x| ≤ w)
    {ℓ a : ℝ} (hℓ : 0 ≤ ℓ) {n : ℕ} (hwa : ((n : ℝ) - 1) / 2 * ℓ + w ≤ a) (c : Fin n → ℂ) :
    tsupport (bumpTest β ℓ c) ⊆ Icc (-a) a := by
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  rw [Function.mem_support, bumpTest] at ht
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  have h1 := hβs _ (right_ne_zero_of_mul hi)
  have h2 := abs_lagPoint_le hℓ i
  have : |t| ≤ a := calc
    |t| = |(t - lagPoint n ℓ i) + lagPoint n ℓ i| := by ring_nf
    _ ≤ |t - lagPoint n ℓ i| + |lagPoint n ℓ i| := abs_add_le _ _
    _ ≤ a := by linarith
  exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- The transform of a lag-point test: `h(z) = (Σ_i c_i e^{izp_i}) h_β(z)`. -/
theorem paperFT_bumpTest {β : ℝ → ℂ} (hβc : Continuous β) (hβcs : HasCompactSupport β) (ℓ : ℝ)
    {n : ℕ} (c : Fin n → ℂ) (z : ℂ) :
    paperFT (bumpTest β ℓ c) z =
      (∑ i : Fin n, c i * cexp (I * z * lagPoint n ℓ i)) * paperFT β z := by
  have hint : ∀ i : Fin n,
      Integrable fun u : ℝ => c i * β (u - lagPoint n ℓ i) * cexp (I * z * u) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact ((hβcs.comp_homeomorph (Homeomorph.subRight (lagPoint n ℓ i))).mul_left).mul_right
  unfold bumpTest paperFT
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := paperFT_comp_sub β (lagPoint n ℓ i) z
  rw [paperFT, paperFT] at h
  simp_rw [mul_assoc (c i)]
  rw [integral_const_mul, h]

/-- **Lag sums of lag-point tests.** For `β` supported in `[-w, w]` with `2w < ℓ`,
`Σ_m k(mℓ) D(m) = (∫ |β|²) · Σ_{i,i'} c_i conj(c_{i'}) D(i − i')`. -/
theorem lagSum_bumpTest_eq_toeplitz {ℓ w : ℝ} (hℓ : 0 < ℓ) (hwℓ : 2 * w < ℓ) {β : ℝ → ℂ}
    (hβc : Continuous β) (hβcs : HasCompactSupport β) (hβs : ∀ x, β x ≠ 0 → |x| ≤ w) {n : ℕ}
    (D : ℤ → ℂ) (c : Fin n → ℂ) :
    ∑' m : ℤ, EF.weilTest (bumpTest β ℓ c) (bumpTest β ℓ c) (m * ℓ) * D m =
      ((∫ x, ‖β x‖ ^ 2 : ℝ) : ℂ) * toeplitzForm D n c := by
  set B : ℝ := ∫ x, ‖β x‖ ^ 2 with hB
  set f := bumpTest β ℓ c with hf
  have hcross : ∀ (m : ℤ) (i i' : Fin n), (∫ t, β (t - lagPoint n ℓ i) *
      conj (β (t - m * ℓ - lagPoint n ℓ i'))) = if (i : ℤ) - i' = m then (B : ℂ) else 0 := by
    intro m i i'
    split_ifs with hm
    · have hsh : ∀ t, t - m * ℓ - lagPoint n ℓ i' = t - lagPoint n ℓ i := by
        intro t
        have := lagPoint_sub n ℓ i i'
        rw [hm] at this
        linarith
      simp_rw [hsh, Complex.mul_conj']
      rw [hB, ← integral_complex_ofReal]
      push_cast
      exact integral_sub_right_eq_self (fun t => ((‖β t‖ : ℝ) : ℂ) ^ 2) _
    · have hz : ∀ t, β (t - lagPoint n ℓ i) * conj (β (t - m * ℓ - lagPoint n ℓ i')) = 0 := by
        intro t
        by_contra hne
        have h1 := hβs _ (left_ne_zero_of_mul hne)
        have h2 := hβs _ (fun h0 => right_ne_zero_of_mul hne (by rw [h0, map_zero]))
        have hk : ((i : ℤ) - i' - m : ℤ) ≠ 0 := sub_ne_zero.mpr hm
        have hk1 : (1 : ℝ) ≤ |(((i : ℤ) - i' - m : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
        have hdiff : (((i : ℤ) - i' - m : ℤ) : ℝ) * ℓ =
            (t - m * ℓ - lagPoint n ℓ i') - (t - lagPoint n ℓ i) := by
          have := lagPoint_sub n ℓ i i'
          push_cast at this ⊢
          linarith
        have : |(((i : ℤ) - i' - m : ℤ) : ℝ) * ℓ| ≤ 2 * w := by
          rw [hdiff]
          calc |(t - m * ℓ - lagPoint n ℓ i') - (t - lagPoint n ℓ i)|
              ≤ |t - m * ℓ - lagPoint n ℓ i'| + |t - lagPoint n ℓ i| := abs_sub _ _
            _ ≤ w + w := add_le_add h2 h1
            _ = 2 * w := by ring
        rw [abs_mul, abs_of_pos hℓ] at this
        nlinarith
      simp_rw [hz, integral_zero]
  have hK : ∀ m : ℤ, EF.weilTest f f (m * ℓ) =
      ∑ i : Fin n, ∑ i' : Fin n, if (i : ℤ) - i' = m then c i * conj (c i') * (B : ℂ) else 0 := by
    intro m
    rw [weilTest_apply]
    have hpt : ∀ t, f t * conj (f (t - m * ℓ)) = ∑ i : Fin n, ∑ i' : Fin n,
        c i * conj (c i') * (β (t - lagPoint n ℓ i) * conj (β (t - m * ℓ - lagPoint n ℓ i'))) := by
      intro t
      rw [hf, bumpTest, bumpTest, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul]
      ring
    simp_rw [hpt]
    have hint : ∀ i i' : Fin n, Integrable fun t => c i * conj (c i') *
        (β (t - lagPoint n ℓ i) * conj (β (t - m * ℓ - lagPoint n ℓ i'))) := by
      intro i i'
      refine Integrable.const_mul ?_ _
      refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
      exact (hβcs.comp_homeomorph (Homeomorph.subRight (lagPoint n ℓ i))).mul_right
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => hint i i']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun i' _ => hint i i']
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [integral_const_mul, hcross m i i']
    split_ifs <;> ring
  have hsum : HasSum (fun m : ℤ => EF.weilTest f f (m * ℓ) * D m)
      (∑ i : Fin n, ∑ i' : Fin n, c i * conj (c i') * (B : ℂ) * D ((i : ℤ) - i')) := by
    have hpt : ∀ m : ℤ, EF.weilTest f f (m * ℓ) * D m = ∑ i : Fin n, ∑ i' : Fin n,
        if m = (i : ℤ) - i' then c i * conj (c i') * (B : ℂ) * D ((i : ℤ) - i') else 0 := by
      intro m
      rw [hK m, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i' _ => ?_
      by_cases h : (i : ℤ) - i' = m
      · rw [if_pos h, if_pos h.symm, h]
      · rw [if_neg h, if_neg (fun h' => h h'.symm), zero_mul]
    simp_rw [hpt]
    exact hasSum_sum fun i _ => hasSum_sum fun i' _ => hasSum_ite_eq _ _
  rw [hsum.tsum_eq, toeplitzForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  ring

/-- **Polar-free bump.** For `0 < w ≤ 1/4` there is a `C²` bump supported in `[-w, w]`, with
transform vanishing at `±i/2` and positive energy: `κ_w'' − κ_w/4`. -/
theorem exists_polarFree_bump {w : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) :
    ∃ β : ℝ → ℂ, ContDiff ℝ 2 β ∧ HasCompactSupport β ∧ (∀ x, β x ≠ 0 → |x| ≤ w) ∧
      paperFT β (I / 2) = 0 ∧ paperFT β (-(I / 2)) = 0 ∧ 0 < ∫ x, ‖β x‖ ^ 2 := by
  have hpole : ∀ z : ℂ, z = I / 2 ∨ z = -(I / 2) → z ^ 2 + 1 / 4 = 0 := by
    rintro z (rfl | rfl) <;> ring_nf <;> rw [Complex.I_sq] <;> ring
  have hβc := contDiff_scaledBumpPolarFree w 0
  have hβcs := hasCompactSupport_scaledBumpPolarFree hw 0
  refine ⟨scaledBumpPolarFree w 0, hβc, hβcs, fun x hx => ?_, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact hx (scaledBumpPolarFree_eq_zero hw h)
  · rw [paperFT_scaledBumpPolarFree hw, hpole _ (Or.inl rfl), neg_zero, zero_mul]
  · rw [paperFT_scaledBumpPolarFree hw, hpole _ (Or.inr rfl), neg_zero, zero_mul]
  · obtain ⟨x, hx⟩ : ∃ x, scaledBumpPolarFree w 0 x ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : paperFT (scaledBumpPolarFree w 0) 0 = 0 := by simp [paperFT, h]
      rw [paperFT_scaledBumpPolarFree hw] at h0
      have hb := norm_paperFT_scaledBump_real_ge hw hw4 (s := 0) (by simp)
      have hpos : 0 < 4 * w * (Real.cos (1 / 8) * ∫ u, weilBump u) := by
        have : 0 < ∫ u, weilBump u := weilBump.integral_pos
        have hc : 0 < Real.cos (1 / 8) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
        positivity
      have hz : paperFT (scaledBump w) ((0 : ℝ) : ℂ) = 0 := by
        have h4 : (-((0 : ℂ) ^ 2 + 1 / 4)) ≠ 0 := by norm_num
        simpa [h4] using h0
      rw [hz, norm_zero] at hb
      linarith
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
      (by have := hβc.continuous; fun_prop)
      (hβcs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)) (fun y => by positivity)
      (by simpa using hx)

/-! ### Polar blindness -/

/-- **Hodge–Toeplitz law.** A configuration with lag formula `W(f, f) = ℓ Σ_m k(mℓ) D(m)` satisfies
the level-`a` Hodge index iff the Toeplitz form of `D` of size `⌈2a/ℓ⌉` is positive semidefinite. -/
theorem hodgeIndex_iff_toeplitz_of_lagFormula (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (D : ℤ → ℂ) (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) :
    HodgeIndexAtLevel Z a ↔
      ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ, 0 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re := by
  constructor
  · intro h c
    by_contra hneg
    push Not at hneg
    have hna : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) * ℓ < 2 * a := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * a / ℓ)
      have : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) < 2 * a / ℓ := by linarith
      rwa [lt_div_iff₀ hℓ] at this
    have hgap : 0 < a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ := by linarith
    obtain ⟨w, hw⟩ : ∃ w : ℝ,
        w = min (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1 / 4 := ⟨_, rfl⟩
    have hw0 : 0 < w := by
      rw [hw]; exact div_pos (lt_min (lt_min (by linarith) hgap) one_pos) (by norm_num)
    have hm1 := min_le_left (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1
    have hm2 := min_le_right (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1
    have hm3 := min_le_left (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)
    have hm4 := min_le_right (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)
    have hwℓ : 2 * w < ℓ := by rw [hw]; linarith
    have hwa : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ + w ≤ a := by rw [hw]; linarith
    have hw4 : 4 * w ≤ 1 := by rw [hw]; linarith
    obtain ⟨β, hβ2, hβcs, hβs, hβp, hβm, hB⟩ := exists_polarFree_bump hw0 hw4
    have hf := contDiff_bumpTest hβ2 ℓ c
    have hfs := tsupport_bumpTest_subset hβs hℓ.le hwa c
    have hpol : ∀ z : ℂ, paperFT β z = 0 → paperFT (bumpTest β ℓ c) z = 0 := fun z hz => by
      rw [paperFT_bumpTest hβ2.continuous hβcs, hz, mul_zero]
    have := h _ hf hfs (hpol _ hβp) (hpol _ hβm)
    rw [hW _ hf (hasCompactSupport_of_tsupport_subset_Icc hfs),
      lagSum_bumpTest_eq_toeplitz hℓ hwℓ hβ2.continuous hβcs hβs, ← mul_assoc,
      show ((ℓ : ℝ) : ℂ) * ((∫ x, ‖β x‖ ^ 2 : ℝ) : ℂ) = ((ℓ * ∫ x, ‖β x‖ ^ 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.re_ofReal_mul] at this
    have hpos : 0 < ℓ * ∫ x, ‖β x‖ ^ 2 := mul_pos hℓ hB
    nlinarith
  · intro hT f hf hfs _ _
    rw [hW f hf (hasCompactSupport_of_tsupport_subset_Icc hfs)]
    exact re_lagSum_nonneg_of_toeplitz hℓ D hT hf hfs

/-- **Polar blindness.** For a configuration with a lag formula, the level-`a` Hodge index is full
Weil positivity at aperture `a`. -/
theorem hodgeIndex_iff_weil_nonneg_of_lagFormula (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (D : ℤ → ℂ) (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) :
    HodgeIndexAtLevel Z a ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re := by
  rw [hodgeIndex_iff_toeplitz_of_lagFormula Z hℓ D hW ha,
    weil_nonneg_iff_toeplitz_of_lagFormula Z hℓ D hW ha]

theorem exists_Icc_of_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    ∃ A : ℝ, tsupport f ⊆ Icc (-(A / 2)) (A / 2) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨2 * R, ?_⟩
  rw [show 2 * R / 2 = R by ring]
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
  exact hR

/-! ### The off-line lattice and periodic profiles -/

/-- Lag formula of the off-line lattice: `W(f, f) = L Σ_m k(mL) 2cosh(δmL)`. -/
theorem W_offLineLatticeConfig_lag {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (offLineLatticeConfig hL hδ hδ').W f f = ((L : ℝ) : ℂ) *
      ∑' m : ℤ, EF.weilTest f f (m * L) * (((2 * Real.cosh (δ * (m * L))) : ℝ) : ℂ) := by
  obtain ⟨A, hfs⟩ := exists_Icc_of_hasCompactSupport hfc
  rw [W_offLineLatticeConfig hL hδ hδ' hf hf.continuous hfs hfs]
  obtain ⟨S, hS⟩ := exists_lag_window (K := EF.weilTest f f) hL (weilTest_abs_le hfs hfs)
  rw [tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul],
    tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul],
    tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul], ← mul_add,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Real.cosh_eq]
  push_cast
  ring_nf

/-- **The off-line lattice masks exactly to `L/2`.** The lattice `{½ ± δ + 2πik/L}` satisfies the
level-`a` Hodge index iff `a ≤ L/2`. -/
theorem offLineLattice_hodgeIndex_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {a : ℝ} (ha : 0 < a) :
    HodgeIndexAtLevel (offLineLatticeConfig hL hδ hδ') a ↔ a ≤ L / 2 := by
  rw [hodgeIndex_iff_weil_nonneg_of_lagFormula _ hL _
    (fun _ hf hfc => W_offLineLatticeConfig_lag hL hδ hδ' hf hfc) ha]
  exact offLineLattice_weil_positive_iff hL hδ hδ' a

/-- Lag formula of a periodic depth profile, for every compactly supported test. -/
theorem W_profileConfig_lag {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (profileConfig hL hP d hd0 hd1).W f f =
      ((L / P : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * (L / P)) * depthSymbol L d m := by
  obtain ⟨A, hfs⟩ := exists_Icc_of_hasCompactSupport hfc
  exact W_profileConfig hL hP d hd0 hd1 hf hfs

/-- **Hodge–Toeplitz law for periodic depth profiles.** -/
theorem profileConfig_hodgeIndex_iff {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ} (ha : 0 < a) :
    HodgeIndexAtLevel (profileConfig hL hP d hd0 hd1) a ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re :=
  hodgeIndex_iff_weil_nonneg_of_lagFormula _ (div_pos hL (by exact_mod_cast hP)) _
    (fun _ hf hfc => W_profileConfig_lag hL hP d hd0 hd1 hf hfc) ha

/-- **Hodge Nyquist ceiling.** A periodic depth profile with an off-line residue violates the
Hodge index at every level `a > L/2`. -/
theorem profileConfig_not_hodgeIndex_of_nyquist_lt {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {r₀ : Fin P}
    (hr₀ : d r₀ ≠ 0) {a : ℝ} (ha : L / 2 < a) :
    ¬ HodgeIndexAtLevel (profileConfig hL hP d hd0 hd1) a := by
  rw [profileConfig_hodgeIndex_iff hL hP d hd0 hd1 (lt_trans (by positivity) ha)]
  intro h
  obtain ⟨f, hf, hfs, hneg⟩ := exists_re_W_profileConfig_neg_of_nyquist_lt hL hP d hd0 hd1 hr₀ ha
  exact absurd (h f hf hfs) (not_le.mpr hneg)

/-! ### Crystal rigidity and jitter for the Hodge index -/

theorem patternConfig_hodgeIndex_iff {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (c d : Fin P → ℝ)
    (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hc : ∀ r r' : Fin P, ∀ j j' : ℤ, c r + j * (2 * π / ℓ) = c r' + j' * (2 * π / ℓ) →
      r = r' ∧ j = j') {a : ℝ} (ha : 0 < a) :
    HodgeIndexAtLevel (patternConfig hℓ c d hd0 hd1) a ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((patternConfig hℓ c d hd0 hd1).W f f).re :=
  hodgeIndex_iff_weil_nonneg_of_lagFormula _ hℓ _
    (fun _ hf hfc => W_patternConfig hℓ c d hd0 hd1 hc hf hfc) ha

/-- **Crystal rigidity for the Hodge index.** A periodic off-line pattern of fixed shape `(θ, d)`,
`P ≥ 1`, satisfies the Hodge index at some level `a > (P−1)ℓ/2` at unboundedly many scales `ℓ` iff
it has uniform depth and crystalline ordinates `P(θ_r − θ_{r'}) ∈ ℤ`. -/
theorem hodgeIndex_frequently_iff_uniform_crystal {P : ℕ} (hP : 0 < P) (θ d : Fin P → ℝ)
    (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j') :
    (∀ ℓ₀ : ℝ, ∃ ℓ : ℝ, ∃ hℓ : 0 < ℓ, ℓ₀ ≤ ℓ ∧ ∃ a : ℝ, ((P : ℝ) - 1) * ℓ / 2 < a ∧
        HodgeIndexAtLevel (patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1) a) ↔
      (∀ r r', d r = d r') ∧ ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k := by
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  constructor
  · intro h
    refine uniform_crystal_of_hiding θ d hd0 hd1 hθ fun ℓ₀ => ?_
    obtain ⟨ℓ, hℓ, hℓ₀, a, ha, hH⟩ := h ℓ₀
    have ha0 : 0 < a := lt_of_le_of_lt (by have := hℓ.le; positivity) ha
    exact ⟨ℓ, hℓ, hℓ₀, a, ha,
      (patternConfig_hodgeIndex_iff hℓ _ d hd0 hd1 (scaledOffset_injective hℓ hθ) ha0).mp hH⟩
  · rintro ⟨hunif, hcr⟩ ℓ₀
    have hℓ : 0 < max ℓ₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨max ℓ₀ 1, hℓ, le_max_left _ _, P * max ℓ₀ 1 / 2, by nlinarith, ?_⟩
    have ha0 : 0 < P * max ℓ₀ 1 / 2 := by positivity
    rw [patternConfig_hodgeIndex_iff hℓ _ d hd0 hd1 (scaledOffset_injective hℓ hθ) ha0]
    exact fun _ hf hfs => uniform_crystal_hides θ d hd0 hd1 hθ hunif hcr hℓ ha0 le_rfl hf hfs

/-- **Hodge visibility below the threshold.** Every periodic off-line pattern other than a uniform
crystal violates the Hodge index, for all large scales `ℓ`, at every level `a > (P−1)ℓ/2`. -/
theorem exists_hodge_violation_of_not_uniform_crystal {P : ℕ} (hP : 0 < P) (θ d : Fin P → ℝ)
    (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hnot : ¬ ((∀ r r', d r = d r') ∧ ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k)) :
    ∃ ℓ₀ : ℝ, ∀ ℓ : ℝ, ∀ hℓ : 0 < ℓ, ℓ₀ ≤ ℓ → ∀ a : ℝ, ((P : ℝ) - 1) * ℓ / 2 < a →
      ¬ HodgeIndexAtLevel (patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1) a := by
  by_contra hcon
  push Not at hcon
  exact hnot ((hodgeIndex_frequently_iff_uniform_crystal hP θ d hd0 hd1 hθ).mp hcon)

/-- **Jitter law for the Hodge index.** On `L/4 < a ≤ L/2` the jittered off-line lattice satisfies
the Hodge index iff `cosh(δL/2) · |sin(εL/2)| ≤ 1`. -/
theorem jitterConfig_hodgeIndex_iff {L δ ε : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hε : |ε| < π / L) {a : ℝ} (ha1 : L / 4 < a) (ha2 : a ≤ L / 2) :
    HodgeIndexAtLevel (jitterConfig hL hδ hδ' ε) a ↔
      Real.cosh (δ * (L / 2)) * |Real.sin (ε * (L / 2))| ≤ 1 := by
  rw [← jitterConfig_weil_nonneg_iff hL hδ hδ' hε ha1 ha2]
  exact patternConfig_hodgeIndex_iff (by positivity) _ _ _ _ (jitterOffset_injective hL hε)
    (lt_trans (by positivity) ha1)

end GaloisForLFunctions.SquareRootThreshold
