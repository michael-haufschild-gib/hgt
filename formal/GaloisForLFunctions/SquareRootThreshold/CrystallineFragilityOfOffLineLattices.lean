import GaloisForLFunctions.SquareRootThreshold.DepthProfileFourierModeLaw

/-!
# Crystalline fragility of off-line lattices

**Abstract Toeplitz law** (`weil_nonneg_iff_toeplitz_of_lagFormula`). Whenever a configuration
has Weil form `W(f, f) = ℓ Σ_m k(mℓ) D(m)` on every compactly supported `C²` test, it is
Weil-nonnegative at aperture `a` iff the Toeplitz matrix of `D` of size `⌈2a/ℓ⌉` is positive
semidefinite. The proof only uses the lag formula: narrow bumps at the lag points for one
direction, periodization into Toeplitz sums of samples for the other.

**Periodic off-line patterns** (`patternConfig`, `W_patternConfig`). Place `P` off-line pairs
`½ ± d_r + i(c_r + 2πj/ℓ)` per period `2π/ℓ`, at arbitrary offsets `c_r`. Poisson summation on
each translate gives the lag formula with symbol `D(m) = Σ_r 2cosh(d_r mℓ) e^{i c_r mℓ}`.

**Jitter law** (`jitterConfig_weil_nonneg_iff`). The off-line lattice of density `L/2π` and depth
`δ` is invisible up to the Nyquist aperture `L/2`. Displace its ordinates alternately by `+ε` and
`−ε`: the period doubles, `ℓ = L/2`, and the first mode is `D(1) = 4i cosh(δL/2) sin(εL/2)`. Hence on
the range `L/4 < a ≤ L/2` the jittered lattice is invisible **iff**

`cosh(δL/2) · |sin(εL/2)| ≤ 1`.

With relative jitter `η = εL/2π`, a lattice of depth `δ` is seen below the square-root threshold as
soon as `cosh(δL/2) sin(πη) > 1`, i.e. once `η ≳ e^{−δL/2}` (`exists_jitter_visible`). The
invisibility of dense off-line configurations up to `L/2` is a crystalline phenomenon: it needs
the ordinates to form an arithmetic progression to relative precision `e^{−δL/2}`. At height `T`
(`L ≈ log T`) this is `T^{−δ/2}`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The abstract Toeplitz law -/

/-- **Bump test for a lag symbol.** Narrow bumps at the lag points turn the lag sum into the
Toeplitz form: `Σ_m k(mℓ) D(m) = B Σ_{i,i'} c_i conj(c_{i'}) D(i − i')`, `B > 0`. -/
theorem exists_test_lagSum_eq_toeplitz {ℓ a : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    (hna : ((n : ℝ) - 1) * ℓ < 2 * a) (D : ℤ → ℂ) (c : Fin n → ℂ) :
    ∃ f : ℝ → ℂ, ∃ B : ℝ, 0 < B ∧ ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m = (B : ℂ) * toeplitzForm D n c := by
  have hgap : 0 < a - ((n : ℝ) - 1) / 2 * ℓ := by linarith
  set w : ℝ := min (ℓ / 2) (a - ((n : ℝ) - 1) / 2 * ℓ) / 2 with hw
  have hw0 : 0 < w := by rw [hw]; exact half_pos (lt_min (by linarith) hgap)
  have hwℓ : 2 * w < ℓ := by
    have := min_le_left (ℓ / 2) (a - ((n : ℝ) - 1) / 2 * ℓ); rw [hw]; linarith
  have hwa : ((n : ℝ) - 1) / 2 * ℓ + w ≤ a := by
    have := min_le_right (ℓ / 2) (a - ((n : ℝ) - 1) / 2 * ℓ); rw [hw]; linarith
  obtain ⟨b, hbr⟩ : ∃ b : ContDiffBump (0 : ℝ), b.rOut = w :=
    ⟨⟨w / 2, w, half_pos hw0, half_lt_self hw0⟩, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ → ℝ, β = ⇑b := ⟨_, rfl⟩
  have hβc : ContDiff ℝ 2 β := hβ ▸ b.contDiff
  have hβs : ∀ x, β x ≠ 0 → |x| < w := by
    intro x hx
    have : x ∈ Function.support b := by rw [← hβ]; exact hx
    rw [b.support_eq, hbr, Metric.mem_ball, Real.dist_eq, sub_zero] at this
    exact this
  have hβcs : HasCompactSupport β := hβ ▸ b.hasCompactSupport
  set B : ℝ := ∫ x, β x * β x with hB
  have hβi : Integrable fun x => β x * β x :=
    (hβc.continuous.mul hβc.continuous).integrable_of_hasCompactSupport hβcs.mul_right
  have hBpos : 0 < B := by
    rw [hB, integral_pos_iff_support_of_nonneg (fun x => mul_self_nonneg (β x)) hβi,
      Function.support_mul, Set.inter_self, hβ, b.support_eq, hbr]
    exact Metric.measure_ball_pos volume 0 hw0
  set f : ℝ → ℂ := fun t => ∑ i : Fin n, c i * (β (t - lagPoint n ℓ i) : ℂ) with hf
  have hfc : ContDiff ℝ 2 f := by
    rw [hf]
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact Complex.ofRealCLM.contDiff.comp (hβc.comp (contDiff_id.sub contDiff_const))
  have hfsupp : ∀ t, f t ≠ 0 → |t| < a := by
    intro t ht
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    have hb : β (t - lagPoint n ℓ i) ≠ 0 := fun h0 => hi (by rw [h0]; simp)
    have h1 := hβs _ hb
    have h2 := abs_lagPoint_le hℓ.le i
    calc |t| = |(t - lagPoint n ℓ i) + lagPoint n ℓ i| := by ring_nf
      _ ≤ |t - lagPoint n ℓ i| + |lagPoint n ℓ i| := abs_add_le _ _
      _ < w + ((n : ℝ) - 1) / 2 * ℓ := by linarith
      _ ≤ a := by linarith
  have hfs : tsupport f ⊆ Icc (-a) a := by
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    have := hfsupp t ht
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨f, B, hBpos, hfc, hfs, ?_⟩
  -- the Weil kernel at the lag lattice
  have hcross : ∀ (m : ℤ) (i i' : Fin n), (∫ t, (β (t - lagPoint n ℓ i) : ℂ) *
      (β (t - m * ℓ - lagPoint n ℓ i') : ℂ)) = if (i : ℤ) - i' = m then (B : ℂ) else 0 := by
    intro m i i'
    split_ifs with hm
    · have hsh : ∀ t, t - m * ℓ - lagPoint n ℓ i' = t - lagPoint n ℓ i := by
        intro t
        have := lagPoint_sub n ℓ i i'
        rw [hm] at this
        linarith
      simp_rw [hsh]
      rw [hB, ← integral_complex_ofReal]
      push_cast
      exact integral_sub_right_eq_self (fun t => ((β t : ℝ) : ℂ) * (β t : ℂ)) _
    · have hz : ∀ t, (β (t - lagPoint n ℓ i) : ℂ) * (β (t - m * ℓ - lagPoint n ℓ i') : ℂ) = 0 := by
        intro t
        by_contra hne
        have h1 := hβs (t - lagPoint n ℓ i) (fun h0 => hne (by rw [h0]; simp))
        have h2 := hβs (t - m * ℓ - lagPoint n ℓ i') (fun h0 => hne (by rw [h0]; simp))
        have hk : ((i : ℤ) - i' - m : ℤ) ≠ 0 := sub_ne_zero.mpr hm
        have hk1 : (1 : ℝ) ≤ |(((i : ℤ) - i' - m : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
        have hdiff : (((i : ℤ) - i' - m : ℤ) : ℝ) * ℓ =
            (t - m * ℓ - lagPoint n ℓ i') - (t - lagPoint n ℓ i) := by
          have := lagPoint_sub n ℓ i i'
          push_cast at this ⊢
          linarith
        have : |(((i : ℤ) - i' - m : ℤ) : ℝ) * ℓ| < 2 * w := by
          rw [hdiff]
          calc |(t - m * ℓ - lagPoint n ℓ i') - (t - lagPoint n ℓ i)|
              ≤ |t - m * ℓ - lagPoint n ℓ i'| + |t - lagPoint n ℓ i| := abs_sub _ _
            _ < w + w := add_lt_add h2 h1
            _ = 2 * w := by ring
        rw [abs_mul, abs_of_pos hℓ] at this
        nlinarith
      simp_rw [hz, integral_zero]
  have hK : ∀ m : ℤ, EF.weilTest f f (m * ℓ) =
      ∑ i : Fin n, ∑ i' : Fin n, if (i : ℤ) - i' = m then c i * conj (c i') * (B : ℂ) else 0 := by
    intro m
    rw [weilTest_apply]
    have hpt : ∀ t, f t * conj (f (t - m * ℓ)) = ∑ i : Fin n, ∑ i' : Fin n,
        c i * conj (c i') * ((β (t - lagPoint n ℓ i) : ℂ) *
          (β (t - m * ℓ - lagPoint n ℓ i') : ℂ)) := by
      intro t
      rw [hf]
      simp only
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul, Complex.conj_ofReal]
      ring
    simp_rw [hpt]
    have hint : ∀ i i' : Fin n, Integrable fun t => c i * conj (c i') *
        ((β (t - lagPoint n ℓ i) : ℂ) * (β (t - m * ℓ - lagPoint n ℓ i') : ℂ)) := by
      intro i i'
      refine Integrable.const_mul ?_ _
      refine ((Complex.continuous_ofReal.comp (hβc.continuous.comp (continuous_id.sub
        continuous_const))).mul (Complex.continuous_ofReal.comp (hβc.continuous.comp
        ((continuous_id.sub continuous_const).sub continuous_const)))).integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.mul_right ?_
      exact (hβcs.comp_homeomorph (Homeomorph.subRight (lagPoint n ℓ i))).comp_left
        Complex.ofReal_zero
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => hint i i']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun i' _ => hint i i']
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [integral_const_mul, hcross m i i']
    split_ifs <;> ring
  -- the lag sum
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

/-- **Periodization bound.** If the Toeplitz form of `D` of size `⌈2a/ℓ⌉` is positive semidefinite,
the lag sum of every test supported in `[-a, a]` has nonnegative real part. -/
theorem re_lagSum_nonneg_of_toeplitz {ℓ a : ℝ} (hℓ : 0 < ℓ) (D : ℤ → ℂ)
    (hT : ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ, 0 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ (((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m).re := by
  set n : ℕ := ⌈2 * a / ℓ⌉₊ with hn
  have hnℓ : 2 * a ≤ n * ℓ := by
    have := Nat.le_ceil (2 * a / ℓ)
    rwa [div_le_iff₀ hℓ] at this
  have hfz : ∀ t, a ≤ |t| → f t = 0 := fun t ht =>
    eq_zero_of_tsupport_subset_Icc hf.continuous hfs ht
  set M : ℕ := ⌈(a + ℓ) / ℓ⌉₊ with hM
  have hMℓ : a + ℓ ≤ M * ℓ := by
    have := Nat.le_ceil ((a + ℓ) / ℓ)
    rwa [div_le_iff₀ hℓ] at this
  rw [lagSum_eq_integral_toeplitzSum hf.continuous hℓ hfz _ hMℓ]
  have hcont : Continuous fun s => toeplitzSum D (Finset.Icc (-(M : ℤ)) M)
      (fun k => f (s + k * ℓ)) := by
    unfold toeplitzSum
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ => ?_
    exact ((hf.continuous.comp (continuous_id.add continuous_const)).mul
      (continuous_conj.comp (hf.continuous.comp (continuous_id.add continuous_const)))).mul
        continuous_const
  rw [intervalIntegral.integral_of_le hℓ.le, Complex.re_ofReal_mul]
  refine mul_nonneg hℓ.le ?_
  rw [show (∫ s in Ioc (0 : ℝ) ℓ, toeplitzSum D (Finset.Icc (-(M : ℤ)) M)
      (fun k => f (s + k * ℓ))).re = ∫ s in Ioc (0 : ℝ) ℓ, (toeplitzSum D
      (Finset.Icc (-(M : ℤ)) M) (fun k => f (s + k * ℓ))).re from
    (integral_re (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).symm]
  refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
  -- the window of the samples at `s`
  set k₀ : ℤ := ⌊(-a - s) / ℓ⌋ + 1 with hk₀
  have hk₀lo : -a < s + k₀ * ℓ := by
    have h := Int.lt_floor_add_one ((-a - s) / ℓ)
    rw [div_lt_iff₀ hℓ] at h
    push_cast [hk₀]
    linarith
  refine re_toeplitzSum_nonneg_of_window hT k₀ (fun j hj => ?_) (fun j hj => ?_)
  · apply hfz
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with h | h
    · have : (j : ℝ) ≤ -M - 1 := by exact_mod_cast (by omega : j ≤ -(M : ℤ) - 1)
      have h1 : (j : ℝ) * ℓ ≤ (-M - 1) * ℓ := mul_le_mul_of_nonneg_right this hℓ.le
      calc a ≤ -(s + j * ℓ) := by linarith [hs.2]
        _ ≤ |s + j * ℓ| := neg_le_abs _
    · have : (M : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : (M : ℤ) + 1 ≤ j)
      have h1 : ((M : ℝ) + 1) * ℓ ≤ j * ℓ := mul_le_mul_of_nonneg_right this hℓ.le
      calc a ≤ s + j * ℓ := by linarith [hs.1]
        _ ≤ |s + j * ℓ| := le_abs_self _
  · apply hfz
    rcases hj with h | h
    · have hj : (j : ℝ) ≤ ⌊(-a - s) / ℓ⌋ := by exact_mod_cast (by omega : j ≤ ⌊(-a - s) / ℓ⌋)
      have h2 : (j : ℝ) ≤ (-a - s) / ℓ := hj.trans (Int.floor_le _)
      rw [le_div_iff₀ hℓ] at h2
      calc a ≤ -(s + j * ℓ) := by linarith
        _ ≤ |s + j * ℓ| := neg_le_abs _
    · have hj : (k₀ : ℝ) + n ≤ j := by exact_mod_cast h
      have h1 : ((k₀ : ℝ) + n) * ℓ ≤ j * ℓ := mul_le_mul_of_nonneg_right hj hℓ.le
      calc a ≤ s + j * ℓ := by nlinarith
        _ ≤ |s + j * ℓ| := le_abs_self _


/-- **Abstract Toeplitz law.** A configuration with lag formula `W(f, f) = ℓ Σ_m k(mℓ) D(m)` is
Weil-nonnegative at aperture `a` iff the Toeplitz form of `D` of size `⌈2a/ℓ⌉` is positive
semidefinite. -/
theorem weil_nonneg_iff_toeplitz_of_lagFormula (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (D : ℤ → ℂ) (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re) ↔
      ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ, 0 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re := by
  constructor
  · intro h c
    by_contra hneg
    push Not at hneg
    have hna : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) * ℓ < 2 * a := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * a / ℓ)
      have : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) < 2 * a / ℓ := by linarith
      rwa [lt_div_iff₀ hℓ] at this
    obtain ⟨f, B, hB, hf, hfs, hlag⟩ := exists_test_lagSum_eq_toeplitz hℓ hna D c
    have := h f hf hfs
    rw [hW f hf (hasCompactSupport_of_tsupport_subset_Icc hfs), hlag, ← mul_assoc,
      show ((ℓ : ℝ) : ℂ) * (B : ℂ) = ((ℓ * B : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul] at this
    have hpos : 0 < ℓ * B := mul_pos hℓ hB
    nlinarith
  · intro hT f hf hfs
    rw [hW f hf (hasCompactSupport_of_tsupport_subset_Icc hfs)]
    exact re_lagSum_nonneg_of_toeplitz hℓ D hT hf hfs


/-! ### Periodic off-line patterns -/

/-- The point `½ + s + i(c + 2πj/ℓ)`. -/
def patternPoint (ℓ s c : ℝ) (j : ℤ) : ℂ := ⟨1 / 2 + s, c + j * (2 * π / ℓ)⟩

theorem gammaOf_patternPoint (ℓ s c : ℝ) (j : ℤ) :
    gammaOf (patternPoint ℓ s c j) = ((c + j * (2 * π / ℓ) : ℝ) : ℂ) - I * s := by
  have hI : I * I = -1 := Complex.I_mul_I
  rw [gammaOf, div_eq_iff Complex.I_ne_zero, patternPoint, Complex.mk_eq_add_mul_I]
  push_cast
  linear_combination (s : ℂ) * hI

theorem reflect_patternPoint (ℓ s c : ℝ) (j : ℤ) :
    reflect (patternPoint ℓ s c j) = patternPoint ℓ (-s) c j := by
  apply Complex.ext
  · simp only [reflect, patternPoint, Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
  · simp only [reflect, patternPoint, Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

/-- `P` off-line pairs of depths `d_r` per ordinate period `2π/ℓ`, at offsets `c_r`. -/
def patternConfig {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (c d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r)
    (hd1 : ∀ r, d r ≤ 1 / 2) : ZeroConfig where
  carrier := (Set.range fun rj : Fin P × ℤ => patternPoint ℓ (d rj.1) (c rj.1) rj.2) ∪
    Set.range fun rj : Fin P × ℤ => patternPoint ℓ (-d rj.1) (c rj.1) rj.2
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro _ (⟨rj, rfl⟩ | ⟨rj, rfl⟩) <;> simp only [patternPoint] <;> constructor <;>
      linarith [hd0 rj.1, hd1 rj.1]
  reflect_mem := by
    rintro _ (⟨rj, rfl⟩ | ⟨rj, rfl⟩)
    · exact Or.inr ⟨rj, (reflect_patternPoint _ _ _ _).symm⟩
    · exact Or.inl ⟨rj, by rw [reflect_patternPoint, neg_neg]⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    set Δ : ℝ := 2 * π / ℓ with hΔ
    have hΔ0 : 0 < Δ := by positivity
    set C : ℝ := ∑ r, |c r| with hC
    have hcC : ∀ r, |c r| ≤ C := fun r =>
      Finset.single_le_sum (f := fun r => |c r|) (fun r _ => abs_nonneg _) (Finset.mem_univ r)
    have hfin : ((Set.univ : Set (Fin P)) ×ˢ
        Set.Icc (⌊(T₁ - C) / Δ⌋) (⌈(T₂ + C) / Δ⌉)).Finite :=
      Set.finite_univ.prod (Set.finite_Icc _ _)
    have hsub : ∀ rj : Fin P × ℤ, T₁ < c rj.1 + rj.2 * Δ → c rj.1 + rj.2 * Δ ≤ T₂ →
        rj ∈ ((Set.univ : Set (Fin P)) ×ˢ Set.Icc (⌊(T₁ - C) / Δ⌋) (⌈(T₂ + C) / Δ⌉)) := by
      intro rj h1 h2
      have hc := abs_le.mp (hcC rj.1)
      simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc]
      constructor
      · have : (T₁ - C) / Δ < rj.2 := by rw [div_lt_iff₀ hΔ0]; linarith
        exact Int.le_of_lt_add_one (by
          have := (Int.floor_le ((T₁ - C) / Δ)).trans_lt this
          exact_mod_cast (show ((⌊(T₁ - C) / Δ⌋ : ℤ) : ℝ) < rj.2 + 1 by linarith))
      · have : (rj.2 : ℝ) ≤ (T₂ + C) / Δ := by rw [le_div_iff₀ hΔ0]; linarith
        exact_mod_cast this.trans (Int.le_ceil _)
    refine ((hfin.image fun rj => patternPoint ℓ (d rj.1) (c rj.1) rj.2).union
      (hfin.image fun rj => patternPoint ℓ (-d rj.1) (c rj.1) rj.2)).subset ?_
    rintro _ ⟨(⟨rj, rfl⟩ | ⟨rj, rfl⟩), h1, h2⟩
    · exact Or.inl ⟨rj, hsub rj h1 h2, rfl⟩
    · exact Or.inr ⟨rj, hsub rj h1 h2, rfl⟩

/-- The pattern symbol `D(m) = Σ_r 2cosh(d_r mℓ) e^{i c_r mℓ}`. -/
def patternSymbol (ℓ : ℝ) {P : ℕ} (c d : Fin P → ℝ) (m : ℤ) : ℂ :=
  ∑ r : Fin P, ((2 * Real.cosh (d r * (m * ℓ))) : ℝ) * cexp (I * c r * (m * ℓ))

/-- A translate of the lattice of spacing `2π/ℓ`: its tilted zero sum is
`ℓ Σ_m k(mℓ) e^{icmℓ} e^{s mℓ}`. -/
theorem hasSum_paperFT_translate {K : ℝ → ℂ} {A ℓ : ℝ} (hℓ : 0 < ℓ) (hK : ContDiff ℝ 2 K)
    (hsupp : ∀ u, K u ≠ 0 → |u| ≤ A) (c s : ℝ) :
    HasSum (fun j : ℤ => paperFT K (((c + j * (2 * π / ℓ) : ℝ) : ℂ) - I * s))
      (((ℓ : ℝ) : ℂ) * ∑' m : ℤ, K (m * ℓ) * cexp (I * c * (m * ℓ)) *
        (Real.exp (s * (m * ℓ)) : ℂ)) := by
  set Kc : ℝ → ℂ := fun u => K u * cexp (I * c * u) with hKc
  have hKcc : ContDiff ℝ 2 Kc := hK.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  have hKcs : ∀ u, Kc u ≠ 0 → |u| ≤ A := fun u hu => hsupp u (left_ne_zero_of_mul hu)
  have h := hasSum_paperFT_lattice_sub_I_mul hℓ hKcc hKcs s
  have hfun : (fun j : ℤ => paperFT Kc ((((j : ℝ) * (2 * π / ℓ)) : ℝ) - I * s)) =
      fun j : ℤ => paperFT K (((c + j * (2 * π / ℓ) : ℝ) : ℂ) - I * s) := by
    funext j
    rw [hKc, ← paperFT_add_ofReal]
    congr 1
    push_cast
    ring
  rw [hfun, show (∑' m : ℤ, Kc (m * ℓ) * (Real.exp (s * (m * ℓ)) : ℂ)) =
      ∑' m : ℤ, K (m * ℓ) * cexp (I * c * (m * ℓ)) * (Real.exp (s * (m * ℓ)) : ℂ) by
    congr 1 with m; simp only [hKc]; push_cast; ring] at h
  exact h

/-- **Lag formula for periodic off-line patterns.**
`W(f, f) = ℓ Σ_m k(mℓ) D(m)` with `D(m) = Σ_r 2cosh(d_r mℓ) e^{i c_r mℓ}`. -/
theorem W_patternConfig {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (c d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r)
    (hd1 : ∀ r, d r ≤ 1 / 2)
    (hc : ∀ r r' : Fin P, ∀ j j' : ℤ, c r + j * (2 * π / ℓ) = c r' + j' * (2 * π / ℓ) →
      r = r' ∧ j = j')
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (patternConfig hℓ c d hd0 hd1).W f f =
      ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * patternSymbol ℓ c d m := by
  set Z := patternConfig hℓ c d hd0 hd1 with hZ
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hfs : tsupport f ⊆ Icc (-(2 * R / 2)) (2 * R / 2) := by
    rw [show 2 * R / 2 = R by ring]
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
    exact hR
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  set K := EF.weilTest f f with hKdef
  -- injectivity of the two parametrizations
  have hinj : ∀ e : Fin P → ℝ, Function.Injective fun rj : Fin P × ℤ =>
      patternPoint ℓ (e rj.1) (c rj.1) rj.2 := by
    intro e rj rj' h
    have him := congrArg Complex.im h
    simp only [patternPoint] at him
    obtain ⟨h1, h2⟩ := hc rj.1 rj'.1 rj.2 rj'.2 him
    exact Prod.ext h1 h2
  have hsum : ∀ e : Fin P → ℝ, HasSum (fun ρ : Set.range (fun rj : Fin P × ℤ =>
      patternPoint ℓ (e rj.1) (c rj.1) rj.2) => Z.Wsummand f f ρ)
      (∑ r : Fin P, ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, K (m * ℓ) * cexp (I * c r * (m * ℓ)) *
        (Real.exp (e r * (m * ℓ)) : ℂ)) := by
    intro e
    rw [(hinj e).hasSum_range_iff]
    refine hasSum_fin_prod fun r => ?_
    have := hasSum_paperFT_translate hℓ hK hKs (c r) (e r)
    refine this.congr_fun fun j => ?_
    simp only [Function.comp_apply, ZeroConfig.Wsummand, hZ, patternConfig, Nat.cast_one,
      one_mul]
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, gammaOf_patternPoint]
  have hp := hsum d
  have hm := hsum fun r => -d r
  have hd : Disjoint (Set.range fun rj : Fin P × ℤ => patternPoint ℓ (d rj.1) (c rj.1) rj.2)
      (Set.range fun rj : Fin P × ℤ => patternPoint ℓ (-d rj.1) (c rj.1) rj.2) := by
    rw [Set.disjoint_left]
    rintro _ ⟨rj, rfl⟩ ⟨rj', hrj'⟩
    have hre := congrArg Complex.re hrj'
    simp only [patternPoint] at hre
    have := hd0 rj.1; have := hd0 rj'.1
    linarith
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd hp hm
  rw [ZeroConfig.W]
  refine hall.tsum_eq.trans ?_
  -- combine the residues on a finite window of lags
  obtain ⟨S, hS⟩ := exists_lag_window (K := K) hℓ hKs
  have hEsum : ∀ (r : Fin P) (x : ℝ), ∑' m : ℤ, K (m * ℓ) * cexp (I * c r * (m * ℓ)) *
      (Real.exp (x * (m * ℓ)) : ℂ) = ∑ m ∈ S, K (m * ℓ) * cexp (I * c r * (m * ℓ)) *
        (Real.exp (x * (m * ℓ)) : ℂ) := fun r x =>
    tsum_eq_sum fun m hm => by rw [hS m hm, zero_mul, zero_mul]
  rw [tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul]]
  simp_rw [hEsum, ← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [patternSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Real.cosh_eq]
  push_cast
  ring_nf

/-! ### The jittered off-line lattice -/

/-- Offsets of the jittered lattice: the even sites shifted by `+ε`, the odd sites by `−ε`. -/
def jitterOffset (L ε : ℝ) : Fin 2 → ℝ := ![ε, 2 * π / L - ε]

/-- The two offsets stay distinct modulo the doubled period when `|ε| < π/L`. -/
theorem jitterOffset_injective {L ε : ℝ} (hL : 0 < L) (hε : |ε| < π / L) :
    ∀ r r' : Fin 2, ∀ j j' : ℤ, jitterOffset L ε r + j * (2 * π / (L / 2)) =
      jitterOffset L ε r' + j' * (2 * π / (L / 2)) → r = r' ∧ j = j' := by
  have hpi := Real.pi_pos
  have hεb := abs_lt.mp hε
  have hcross : ∀ j j' : ℤ, ε + j * (2 * π / (L / 2)) ≠ 2 * π / L - ε + j' * (2 * π / (L / 2)) := by
    intro j j' h
    have h2 : 2 * ε = (2 * π / L) * (1 + 2 * (j' - j)) := by
      have : 2 * π / (L / 2) = 2 * (2 * π / L) := by field_simp
      rw [this] at h; linarith
    have hk : (1 + 2 * ((j' : ℝ) - j)) = ((1 + 2 * (j' - j) : ℤ) : ℝ) := by push_cast; ring
    rw [hk] at h2
    have hodd : (1 + 2 * (j' - j) : ℤ) ≠ 0 := by omega
    have hab : (1 : ℝ) ≤ |((1 + 2 * (j' - j) : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hodd
    have : |2 * ε| < 2 * π / L := by
      rw [abs_mul, abs_two]
      have := abs_lt.mpr hεb
      linarith [show 2 * (π / L) = 2 * π / L by ring]
    rw [h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π / L)] at this
    nlinarith [show (0 : ℝ) < 2 * π / L by positivity]
  have hper : ∀ (x : ℝ) (j j' : ℤ), x + j * (2 * π / (L / 2)) = x + j' * (2 * π / (L / 2)) →
      j = j' := by
    intro x j j' h
    have hne : (2 * π / (L / 2)) ≠ 0 := by positivity
    exact_mod_cast mul_right_cancel₀ hne (by linarith : (j : ℝ) * (2 * π / (L / 2)) =
      j' * (2 * π / (L / 2)))
  intro r r' j j' h
  fin_cases r <;> fin_cases r' <;> simp only [jitterOffset, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] at h ⊢
  · exact ⟨trivial, hper _ _ _ h⟩
  · exact absurd h (hcross j j')
  · exact absurd h.symm (hcross j' j)
  · exact ⟨trivial, hper _ _ _ h⟩

/-- The jittered off-line lattice: depth `δ` at the sites `2πk/L + (−1)^k ε`. -/
def jitterConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (ε : ℝ) : ZeroConfig :=
  patternConfig (ℓ := L / 2) (by positivity) (jitterOffset L ε) (fun _ => δ) (fun _ => hδ)
    (fun _ => hδ')

/-- The first mode of the jittered lattice: `D(1) = 4i cosh(δL/2) sin(εL/2)`. -/
theorem patternSymbol_jitter_one (L δ ε : ℝ) (hL : 0 < L) :
    ‖patternSymbol (L / 2) (jitterOffset L ε) (fun _ => δ) 1‖ =
      4 * Real.cosh (δ * (L / 2)) * |Real.sin (ε * (L / 2))| := by
  rw [patternSymbol, Fin.sum_univ_two]
  simp only [jitterOffset, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Int.cast_one, one_mul]
  have he : cexp (I * ((2 * π / L - ε : ℝ) : ℂ) * ((L / 2 : ℝ) : ℂ)) =
      -cexp (-(I * (ε : ℂ) * ((L / 2 : ℝ) : ℂ))) := by
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [show I * ((2 * π / L - ε : ℝ) : ℂ) * ((L / 2 : ℝ) : ℂ) =
      π * I + -(I * (ε : ℂ) * ((L / 2 : ℝ) : ℂ)) by push_cast; field_simp; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [he, show ((2 * Real.cosh (δ * (L / 2)) : ℝ) : ℂ) * cexp (I * (ε : ℂ) * ((L / 2 : ℝ) : ℂ)) +
      ((2 * Real.cosh (δ * (L / 2)) : ℝ) : ℂ) * -cexp (-(I * (ε : ℂ) * ((L / 2 : ℝ) : ℂ))) =
      ((4 * Real.cosh (δ * (L / 2)) : ℝ) : ℂ) * (((Real.sin (ε * (L / 2)) : ℝ) : ℂ) * I) by
    rw [Complex.ofReal_sin, Complex.sin]
    push_cast
    rw [show (ε : ℂ) * (L / 2) * I = I * ε * (L / 2) by ring,
      show -((ε : ℂ) * (L / 2)) * I = -(I * ε * (L / 2)) by ring]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring]
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (Real.cosh_pos _)]

/-- **Jitter law.** On the aperture range `L/4 < a ≤ L/2` the jittered off-line lattice is
Weil-nonnegative iff `cosh(δL/2) · |sin(εL/2)| ≤ 1`. The unjittered lattice (`ε = 0`) hides up to
`L/2`; any jitter is amplified by `cosh(δL/2)`. -/
theorem jitterConfig_weil_nonneg_iff {L δ ε : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hε : |ε| < π / L) {a : ℝ} (ha1 : L / 4 < a) (ha2 : a ≤ L / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((jitterConfig hL hδ hδ' ε).W f f).re) ↔
      Real.cosh (δ * (L / 2)) * |Real.sin (ε * (L / 2))| ≤ 1 := by
  have hℓ : (0 : ℝ) < L / 2 := by positivity
  have ha : 0 < a := lt_trans (by positivity) ha1
  rw [weil_nonneg_iff_toeplitz_of_lagFormula (jitterConfig hL hδ hδ' ε) hℓ _
    (fun f hf hfc => W_patternConfig hℓ _ _ _ _ (jitterOffset_injective hL hε) hf hfc) ha]
  have hn : ⌈2 * a / (L / 2)⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · rw [lt_div_iff₀ hℓ]; push_cast; linarith
    · rw [div_le_iff₀ hℓ]; push_cast; linarith
  rw [hn, toeplitzForm_two_nonneg_iff]
  · have h0 : patternSymbol (L / 2) (jitterOffset L ε) (fun _ => δ) 0 = 4 := by
      simp [patternSymbol, Fin.sum_univ_two]; norm_num
    rw [h0, patternSymbol_jitter_one L δ ε hL, Complex.re_ofNat]
    constructor <;> intro h <;> linarith
  · rw [patternSymbol, patternSymbol, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    · congr 2
      rw [Int.cast_neg, Int.cast_one, neg_one_mul, one_mul, mul_neg, Real.cosh_neg]
    · congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
      push_cast
      ring

/-- **Crystalline fragility.** For every depth `δ` and relative jitter `0 < η < ½`, the lattice with
jitter `ε = 2πη/L` is visible at the Nyquist aperture `L/2` as soon as
`cosh(δL/2) sin(πη) > 1`. -/
theorem jitterConfig_visible {L δ η : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hη : 0 < η) (hη' : η < 1 / 2) (hcond : 1 < Real.cosh (δ * (L / 2)) * Real.sin (π * η)) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-(L / 2)) (L / 2) ∧
      ((jitterConfig hL hδ hδ' (2 * π * η / L)).W f f).re < 0 := by
  have hpi := Real.pi_pos
  have hε : |2 * π * η / L| < π / L := by
    rw [abs_of_pos (by positivity), div_lt_div_iff_of_pos_right hL]; nlinarith
  have hiff := jitterConfig_weil_nonneg_iff hL hδ hδ' hε (a := L / 2) (by linarith) le_rfl
  by_contra hcon
  push Not at hcon
  have := hiff.mp hcon
  rw [show 2 * π * η / L * (L / 2) = π * η by field_simp, abs_of_pos (Real.sin_pos_of_pos_of_lt_pi
    (by positivity) (by nlinarith))] at this
  linarith

end GaloisForLFunctions.SquareRootThreshold
