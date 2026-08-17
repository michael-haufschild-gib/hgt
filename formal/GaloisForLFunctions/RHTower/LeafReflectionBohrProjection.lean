import Mathlib
import GaloisForLFunctions.HTGeometry.VitaliConvergence

/-!
# Leaf-reflection Bohr projection catastrophe

Let `α, β, w > 0` with `β/α` irrational, and let `G` be an even entire function which on the
lower flank `Im z ≤ -w` is represented by an absolutely convergent two-base exponential series

`G(z) = ∑_{m,n ≥ 0} b_{m,n} e^{-i z (mα + nβ)}`,  `∑ |b_{m,n}| e^{-w(mα+nβ)} < ∞`.

For `T_α = 2π/α` and `θ = 2πβ/α`, the exact-period transverse Cesàro projector of level `r` is

`P_{r,N}G(z) = N⁻¹ ∑_{k<N} e^{i k r θ} G(z + k T_α)`.

The main theorem (`leaf_reflection_bohr_projection_catastrophe`) says: for `r ≥ 1`, if the
transverse slice `B_r(z) = ∑_m b_{m,r} e^{-i z (mα+rβ)}` is not identically zero on the open
lower flank, then the family `{P_{r,N}G}` is **not locally bounded** on any connected open set
meeting both `{Im z < -w}` and `{Im z > w}`.  The two reflected flanks therefore lie in distinct
normality domains.

The proof is exactly the one on the card:

* `tendsto_proj_lower` — on the lower flank, irrational-rotation Cesàro orthogonality makes the
  `(m,n)` mode acquire the mean `N⁻¹ ∑_{k<N} e^{ik(r-n)θ}`, which tends to `1` for `n = r` and to
  `0` otherwise; dominated convergence gives `P_{r,N}G → B_r` pointwise.
* `tendsto_proj_upper` — on the upper flank, evenness reflects the argument back into the lower
  flank and the mean becomes `N⁻¹ ∑_{k<N} e^{ik(r+n)θ}`, which tends to `0` for every `n ≥ 0`
  because `r ≥ 1`; hence `P_{r,N}G → 0` pointwise.
* `exists_limit_of_locallyBounded` — a locally bounded holomorphic family on a connected open set
  which converges on one ball converges on the whole set, with holomorphic limit.  This is the
  normal-family (Montel/Vitali) input, obtained from the in-tree Vitali theorem by a clopen
  chaining argument.
* `flank_limits_incompatible` — the identity theorem then forces `B_r ≡ 0`, contradiction.

`slice_ne_zero_of_coeff_ne_zero` supplies the last sentence of the card's proof: a single nonzero
coefficient `b_{m₀,r}` makes `B_r` nonzero, because the same Cesàro extraction run in the second
base recovers each individual coefficient.  `leaf_reflection_catastrophe_of_coeff` is the
resulting coefficient form of the theorem.

Only irrationality of `β/α` is used: no Diophantine (continued-fraction) hypothesis enters.
-/

namespace GaloisForLFunctions.LeafReflectionProjection

open Complex Filter Topology Set Metric

noncomputable section



/-! ## Step 1: Cesàro means of a unimodular character -/

/-- The Cesàro mean of the geometric character `k ↦ ζ ^ k`. -/
noncomputable def cesaro (ζ : ℂ) (N : ℕ) : ℂ := (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, ζ ^ k

theorem cesaro_one (N : ℕ) (hN : N ≠ 0) : cesaro 1 N = 1 := by
  simp [cesaro, Finset.sum_const, hN]

theorem tendsto_cesaro_one : Tendsto (cesaro 1) atTop (𝓝 1) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (cesaro_one N (by omega)).symm

theorem norm_cesaro_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (N : ℕ) : ‖cesaro ζ N‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [cesaro, h]
  · have hsum : ‖∑ k ∈ Finset.range N, ζ ^ k‖ ≤ (N : ℝ) := by
      calc ‖∑ k ∈ Finset.range N, ζ ^ k‖ ≤ ∑ k ∈ Finset.range N, ‖ζ ^ k‖ :=
            norm_sum_le _ _
        _ = (N : ℝ) := by simp [norm_pow, hζ]
    have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h
    rw [cesaro, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hN]
    simpa using hsum

theorem tendsto_cesaro_of_ne_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ 1) :
    Tendsto (cesaro ζ) atTop (𝓝 0) := by
  have hd : ζ - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hdpos : (0 : ℝ) < ‖ζ - 1‖ := norm_pos_iff.mpr hd
  have hbd : ∀ N : ℕ, ‖cesaro ζ N‖ ≤ (2 / ‖ζ - 1‖) / N := by
    intro N
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [cesaro, h]
    have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h
    have hgeo : ∑ k ∈ Finset.range N, ζ ^ k = (ζ ^ N - 1) / (ζ - 1) := geom_sum_eq hne N
    have hnum : ‖ζ ^ N - 1‖ ≤ 2 := by
      have h1 : ‖ζ ^ N - 1‖ ≤ ‖ζ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      have h2 : ‖ζ ^ N‖ = 1 := by rw [norm_pow, hζ, one_pow]
      rw [h2] at h1
      have : ‖(1:ℂ)‖ = 1 := norm_one
      rw [this] at h1
      linarith
    have hsum : ‖∑ k ∈ Finset.range N, ζ ^ k‖ ≤ 2 / ‖ζ - 1‖ := by
      rw [hgeo, norm_div]
      gcongr
    rw [cesaro, norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hlim : Tendsto (fun N : ℕ => (2 / ‖ζ - 1‖) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  exact squeeze_zero_norm hbd hlim

/-! ## Step 2: irrational rotation characters -/

theorem exp_int_rot_ne_one {α β : ℝ} (hirr : Irrational (β / α)) {j : ℤ}
    (hj : j ≠ 0) :
    Complex.exp (I * (((j : ℝ) * (2 * Real.pi * β / α) : ℝ) : ℂ)) ≠ 1 := by
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  have hn' : I * (((j : ℝ) * (2 * Real.pi * β / α) : ℝ) : ℂ)
      = I * ((n : ℂ) * (2 * (Real.pi : ℂ))) := by rw [hn]; ring
  have h2 : (((j : ℝ) * (2 * Real.pi * β / α) : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) :=
    mul_left_cancel₀ Complex.I_ne_zero hn'
  have h3 : (j : ℝ) * (2 * Real.pi * β / α) = (n : ℝ) * (2 * Real.pi) := by
    exact_mod_cast h2
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h4 : (β / α) * (j : ℝ) = (n : ℝ) := by
    have : (2 * Real.pi) * ((β / α) * (j : ℝ)) = (2 * Real.pi) * (n : ℝ) := by
      linear_combination h3
    exact mul_left_cancel₀ hpi this
  have hirr' : Irrational ((β / α) * (j : ℤ)) := irrational_mul_intCast_iff.mpr ⟨hj, hirr⟩
  exact Irrational.ne_int hirr' n h4

theorem norm_exp_rot {x : ℝ} : ‖Complex.exp (I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x


/-! ## Step 3: the two-base flank carrier -/

/-- Frequency of the `(m,n)` mode. -/
def freq (α β : ℝ) (mn : ℕ × ℕ) : ℝ := (mn.1 : ℝ) * α + (mn.2 : ℝ) * β

/-- A single exponential mode of the carrier. -/
noncomputable def modeTerm (α β : ℝ) (b : ℕ × ℕ → ℂ) (mn : ℕ × ℕ) (z : ℂ) : ℂ :=
  b mn * Complex.exp (-I * z * ((freq α β mn : ℝ) : ℂ))

/-- The exact period `2π/α` of the first base. -/
def per (α : ℝ) : ℝ := 2 * Real.pi / α

/-- The transverse rotation angle `2πβ/α`. -/
def rot (α β : ℝ) : ℝ := 2 * Real.pi * β / α

/-- The transverse character of level `j`. -/
noncomputable def chi (α β : ℝ) (j : ℤ) : ℂ :=
  Complex.exp (I * (((j : ℝ) * rot α β : ℝ) : ℂ))

theorem norm_chi (α β : ℝ) (j : ℤ) : ‖chi α β j‖ = 1 := norm_exp_rot

theorem chi_zero (α β : ℝ) : chi α β 0 = 1 := by simp [chi]

theorem chi_ne_one {α β : ℝ} (hirr : Irrational (β / α)) {j : ℤ} (hj : j ≠ 0) :
    chi α β j ≠ 1 := exp_int_rot_ne_one hirr hj

theorem freq_nonneg {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (mn : ℕ × ℕ) : 0 ≤ freq α β mn := by
  have h1 : 0 ≤ (mn.1 : ℝ) * α := mul_nonneg (Nat.cast_nonneg _) hα
  have h2 : 0 ≤ (mn.2 : ℝ) * β := mul_nonneg (Nat.cast_nonneg _) hβ
  simpa [freq] using add_nonneg h1 h2

theorem norm_modeTerm (α β : ℝ) (b : ℕ × ℕ → ℂ) (mn : ℕ × ℕ) (z : ℂ) :
    ‖modeTerm α β b mn z‖ = ‖b mn‖ * Real.exp (freq α β mn * z.im) := by
  rw [modeTerm, norm_mul, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring


/-! ## Step 4: period shifts pick up the transverse character -/

theorem modeTerm_add_period {α β : ℝ} (hα : α ≠ 0) (b : ℕ × ℕ → ℂ) (mn : ℕ × ℕ) (k : ℕ)
    (z : ℂ) :
    modeTerm α β b mn (z + (((k : ℝ) * per α : ℝ) : ℂ))
      = modeTerm α β b mn z * (chi α β (-(mn.2 : ℤ))) ^ k := by
  have harg : (-I * (z + (((k : ℝ) * per α : ℝ) : ℂ)) * ((freq α β mn : ℝ) : ℂ))
      = (-I * z * ((freq α β mn : ℝ) : ℂ))
        + ((-((k * mn.1 : ℕ) : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I)
        + (k : ℂ) * (I * ((((-(mn.2 : ℤ) : ℤ) : ℝ) * rot α β : ℝ) : ℂ)) := by
    have hαC : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
    simp only [per, rot, freq]
    push_cast
    field_simp
    ring
  rw [modeTerm, modeTerm, harg, Complex.exp_add, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, Complex.exp_nat_mul, chi]
  ring

theorem modeTerm_sub_period {α β : ℝ} (hα : α ≠ 0) (b : ℕ × ℕ → ℂ) (mn : ℕ × ℕ) (k : ℕ)
    (z : ℂ) :
    modeTerm α β b mn (z - (((k : ℝ) * per α : ℝ) : ℂ))
      = modeTerm α β b mn z * (chi α β ((mn.2 : ℤ))) ^ k := by
  have harg : (-I * (z - (((k : ℝ) * per α : ℝ) : ℂ)) * ((freq α β mn : ℝ) : ℂ))
      = (-I * z * ((freq α β mn : ℝ) : ℂ))
        + (((((k * mn.1 : ℕ) : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I)
        + (k : ℂ) * (I * (((((mn.2 : ℤ) : ℤ) : ℝ) * rot α β : ℝ) : ℂ)) := by
    have hαC : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
    simp only [per, rot, freq]
    push_cast
    field_simp
    ring
  rw [modeTerm, modeTerm, harg, Complex.exp_add, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, Complex.exp_nat_mul, chi]
  ring

/-! ## Step 5: summability on the closed lower flank -/

/-- The dominating bound attached to the flank hypothesis. -/
noncomputable def flankBound (α β w : ℝ) (b : ℕ × ℕ → ℂ) (mn : ℕ × ℕ) : ℝ :=
  ‖b mn‖ * Real.exp (-w * freq α β mn)

theorem norm_modeTerm_le {α β w : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ℕ × ℕ → ℂ)
    (mn : ℕ × ℕ) {z : ℂ} (hz : z.im ≤ -w) :
    ‖modeTerm α β b mn z‖ ≤ flankBound α β w b mn := by
  rw [norm_modeTerm, flankBound]
  have hf : 0 ≤ freq α β mn := freq_nonneg hα hβ mn
  have hmul : freq α β mn * z.im ≤ freq α β mn * (-w) := by
    exact mul_le_mul_of_nonneg_left hz hf
  have hexp : Real.exp (freq α β mn * z.im) ≤ Real.exp (-w * freq α β mn) := by
    apply Real.exp_le_exp.mpr
    calc freq α β mn * z.im ≤ freq α β mn * (-w) := hmul
      _ = -w * freq α β mn := by ring
  exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)

theorem summable_modeTerm {α β w : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {b : ℕ × ℕ → ℂ}
    (hb : Summable (flankBound α β w b)) {z : ℂ} (hz : z.im ≤ -w) :
    Summable (fun mn => modeTerm α β b mn z) :=
  Summable.of_norm_bounded hb (fun mn => norm_modeTerm_le hα hβ b mn hz)


theorem chi_add (α β : ℝ) (j₁ j₂ : ℤ) : chi α β (j₁ + j₂) = chi α β j₁ * chi α β j₂ := by
  rw [chi, chi, chi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_chi_pow (α β : ℝ) (j : ℤ) (k : ℕ) : ‖chi α β j ^ k‖ = 1 := by
  rw [norm_pow, norm_chi, one_pow]

theorem summable_modeTerm_mul {α β w : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {b : ℕ × ℕ → ℂ}
    (hb : Summable (flankBound α β w b)) {z : ℂ} (hz : z.im ≤ -w) (c : ℕ × ℕ → ℂ)
    (hc : ∀ mn, ‖c mn‖ ≤ 1) :
    Summable (fun mn => modeTerm α β b mn z * c mn) := by
  refine Summable.of_norm_bounded hb (fun mn => ?_)
  rw [norm_mul]
  calc ‖modeTerm α β b mn z‖ * ‖c mn‖ ≤ ‖modeTerm α β b mn z‖ * 1 :=
        mul_le_mul_of_nonneg_left (hc mn) (norm_nonneg _)
    _ = ‖modeTerm α β b mn z‖ := mul_one _
    _ ≤ flankBound α β w b mn := norm_modeTerm_le hα hβ b mn hz

/-! ## Step 6: the exact-period transverse projector -/

/-- The exact-period Cesàro projector of transverse level `r`. -/
noncomputable def proj (α β : ℝ) (r : ℕ) (G : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
    chi α β (r : ℤ) ^ k * G (z + (((k : ℝ) * per α : ℝ) : ℂ))

/-- The projector in the form displayed on the card:
`P_{r,N}G(z) = N⁻¹ ∑_{k<N} e^{i k r θ} G(z + k T_α)`. -/
theorem proj_eq_character_form (α β : ℝ) (r : ℕ) (G : ℂ → ℂ) (N : ℕ) (z : ℂ) :
    proj α β r G N z = (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
      Complex.exp (I * (((k : ℝ) * ((r : ℝ) * rot α β) : ℝ) : ℂ))
        * G (z + (((k : ℝ) * per α : ℝ) : ℂ)) := by
  rw [proj]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  rw [chi, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The transverse `r`-slice of the carrier, as a sum over all modes. -/
noncomputable def sliceTerm (α β : ℝ) (b : ℕ × ℕ → ℂ) (r : ℕ) (mn : ℕ × ℕ) (z : ℂ) : ℂ :=
  if mn.2 = r then modeTerm α β b mn z else 0

/-- `B_r`, the transverse `r`-slice. -/
noncomputable def slice (α β : ℝ) (b : ℕ × ℕ → ℂ) (r : ℕ) (z : ℂ) : ℂ :=
  ∑' mn, sliceTerm α β b r mn z


theorem norm_modeTerm_mul_le {α β w : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ℕ × ℕ → ℂ)
    {z : ℂ} (hz : z.im ≤ -w) {c : ℂ} (hc : ‖c‖ ≤ 1) (mn : ℕ × ℕ) :
    ‖modeTerm α β b mn z * c‖ ≤ flankBound α β w b mn := by
  rw [norm_mul]
  calc ‖modeTerm α β b mn z‖ * ‖c‖ ≤ ‖modeTerm α β b mn z‖ * 1 :=
        mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = ‖modeTerm α β b mn z‖ := mul_one _
    _ ≤ flankBound α β w b mn := norm_modeTerm_le hα hβ b mn hz

/-! ## Step 7: the lower flank -- the projector extracts the `r`-slice -/

theorem proj_eq_tsum_lower {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b)) {G : ℂ → ℂ}
    (hG : ∀ y : ℂ, y.im ≤ -w → G y = ∑' mn : ℕ × ℕ, modeTerm α β b mn y)
    (r N : ℕ) {z : ℂ} (hz : z.im ≤ -w) :
    proj α β r G N z
      = ∑' mn : ℕ × ℕ, modeTerm α β b mn z * cesaro (chi α β ((r : ℤ) - (mn.2 : ℤ))) N := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hterm : ∀ k : ℕ, chi α β (r : ℤ) ^ k * G (z + (((k : ℝ) * per α : ℝ) : ℂ))
      = ∑' mn : ℕ × ℕ, modeTerm α β b mn z * chi α β ((r : ℤ) - (mn.2 : ℤ)) ^ k := by
    intro k
    have him : (z + (((k : ℝ) * per α : ℝ) : ℂ)).im ≤ -w := by simpa using hz
    rw [hG _ him]
    have h1 : ∑' mn : ℕ × ℕ, modeTerm α β b mn (z + (((k : ℝ) * per α : ℝ) : ℂ))
        = ∑' mn : ℕ × ℕ, modeTerm α β b mn z * chi α β (-(mn.2 : ℤ)) ^ k :=
      tsum_congr (fun mn => modeTerm_add_period hαne b mn k z)
    rw [h1, ← tsum_mul_left]
    refine tsum_congr (fun mn => ?_)
    have hchi : chi α β ((r : ℤ) - (mn.2 : ℤ)) = chi α β (r : ℤ) * chi α β (-(mn.2 : ℤ)) := by
      have hz2 : (r : ℤ) - (mn.2 : ℤ) = (r : ℤ) + (-(mn.2 : ℤ)) := by ring
      rw [hz2, chi_add]
    rw [hchi, mul_pow]
    ring
  have hsum2 : ∀ k ∈ Finset.range N,
      Summable (fun mn : ℕ × ℕ => modeTerm α β b mn z * chi α β ((r : ℤ) - (mn.2 : ℤ)) ^ k) :=
    fun k _ => summable_modeTerm_mul hα.le hβ.le hb hz _
      (fun mn => le_of_eq (norm_chi_pow α β _ k))
  rw [proj, Finset.sum_congr rfl (fun k _ => hterm k), ← Summable.tsum_finsetSum hsum2,
    ← tsum_mul_left]
  refine tsum_congr (fun mn => ?_)
  rw [cesaro, ← Finset.mul_sum]
  ring

theorem tendsto_proj_lower {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β) (hirr : Irrational (β / α))
    {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b)) {G : ℂ → ℂ}
    (hG : ∀ y : ℂ, y.im ≤ -w → G y = ∑' mn : ℕ × ℕ, modeTerm α β b mn y)
    (r : ℕ) {z : ℂ} (hz : z.im ≤ -w) :
    Tendsto (fun N => proj α β r G N z) atTop (𝓝 (slice α β b r z)) := by
  have heq : ∀ N : ℕ, proj α β r G N z
      = ∑' mn : ℕ × ℕ, modeTerm α β b mn z * cesaro (chi α β ((r : ℤ) - (mn.2 : ℤ))) N :=
    fun N => proj_eq_tsum_lower hα hβ hb hG r N hz
  rw [show (fun N : ℕ => proj α β r G N z)
      = fun N : ℕ => ∑' mn : ℕ × ℕ, modeTerm α β b mn z
          * cesaro (chi α β ((r : ℤ) - (mn.2 : ℤ))) N from funext heq, slice]
  refine tendsto_tsum_of_dominated_convergence hb (fun mn => ?_) ?_
  · by_cases h : mn.2 = r
    · have hj : (r : ℤ) - (mn.2 : ℤ) = 0 := by rw [h]; ring
      have hlim : Tendsto (fun N : ℕ => cesaro (chi α β ((r : ℤ) - (mn.2 : ℤ))) N) atTop (𝓝 1) := by
        rw [hj, chi_zero]; exact tendsto_cesaro_one
      have := hlim.const_mul (modeTerm α β b mn z)
      rw [mul_one] at this
      simpa [sliceTerm, h] using this
    · have hj : (r : ℤ) - (mn.2 : ℤ) ≠ 0 := by
        intro hc
        exact h (by omega)
      have hlim : Tendsto (fun N : ℕ => cesaro (chi α β ((r : ℤ) - (mn.2 : ℤ))) N) atTop (𝓝 0) :=
        tendsto_cesaro_of_ne_one (norm_chi _ _ _) (chi_ne_one hirr hj)
      have := hlim.const_mul (modeTerm α β b mn z)
      rw [mul_zero] at this
      simpa [sliceTerm, h] using this
  · filter_upwards with N mn
    exact norm_modeTerm_mul_le hα.le hβ.le b hz (norm_cesaro_le (norm_chi _ _ _) N) mn


/-! ## Step 8: the upper flank -- the reflected projector annihilates every mode -/

theorem proj_eq_tsum_upper {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b)) {G : ℂ → ℂ}
    (hG : ∀ y : ℂ, y.im ≤ -w → G y = ∑' mn : ℕ × ℕ, modeTerm α β b mn y)
    (hev : ∀ y : ℂ, G (-y) = G y)
    (r N : ℕ) {z : ℂ} (hz : w ≤ z.im) :
    proj α β r G N z
      = ∑' mn : ℕ × ℕ, modeTerm α β b mn (-z) * cesaro (chi α β ((r : ℤ) + (mn.2 : ℤ))) N := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hzneg : (-z).im ≤ -w := by
    have : (-z).im = -z.im := by simp
    rw [this]; linarith
  have hterm : ∀ k : ℕ, chi α β (r : ℤ) ^ k * G (z + (((k : ℝ) * per α : ℝ) : ℂ))
      = ∑' mn : ℕ × ℕ, modeTerm α β b mn (-z) * chi α β ((r : ℤ) + (mn.2 : ℤ)) ^ k := by
    intro k
    have hrefl : G (z + (((k : ℝ) * per α : ℝ) : ℂ))
        = G ((-z) - (((k : ℝ) * per α : ℝ) : ℂ)) := by
      have hneg : (-z) - (((k : ℝ) * per α : ℝ) : ℂ) = -(z + (((k : ℝ) * per α : ℝ) : ℂ)) := by
        ring
      rw [hneg, hev]
    have him : ((-z) - (((k : ℝ) * per α : ℝ) : ℂ)).im ≤ -w := by simpa using hzneg
    rw [hrefl, hG _ him]
    have h1 : ∑' mn : ℕ × ℕ, modeTerm α β b mn ((-z) - (((k : ℝ) * per α : ℝ) : ℂ))
        = ∑' mn : ℕ × ℕ, modeTerm α β b mn (-z) * chi α β ((mn.2 : ℤ)) ^ k :=
      tsum_congr (fun mn => modeTerm_sub_period hαne b mn k (-z))
    rw [h1, ← tsum_mul_left]
    refine tsum_congr (fun mn => ?_)
    rw [chi_add, mul_pow]
    ring
  have hsum2 : ∀ k ∈ Finset.range N,
      Summable (fun mn : ℕ × ℕ => modeTerm α β b mn (-z) * chi α β ((r : ℤ) + (mn.2 : ℤ)) ^ k) :=
    fun k _ => summable_modeTerm_mul hα.le hβ.le hb hzneg _
      (fun mn => le_of_eq (norm_chi_pow α β _ k))
  rw [proj, Finset.sum_congr rfl (fun k _ => hterm k), ← Summable.tsum_finsetSum hsum2,
    ← tsum_mul_left]
  refine tsum_congr (fun mn => ?_)
  rw [cesaro, ← Finset.mul_sum]
  ring

theorem tendsto_proj_upper {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β) (hirr : Irrational (β / α))
    {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b)) {G : ℂ → ℂ}
    (hG : ∀ y : ℂ, y.im ≤ -w → G y = ∑' mn : ℕ × ℕ, modeTerm α β b mn y)
    (hev : ∀ y : ℂ, G (-y) = G y)
    {r : ℕ} (hr : 1 ≤ r) {z : ℂ} (hz : w ≤ z.im) :
    Tendsto (fun N => proj α β r G N z) atTop (𝓝 0) := by
  have hzneg : (-z).im ≤ -w := by
    have : (-z).im = -z.im := by simp
    rw [this]; linarith
  have heq : ∀ N : ℕ, proj α β r G N z
      = ∑' mn : ℕ × ℕ, modeTerm α β b mn (-z) * cesaro (chi α β ((r : ℤ) + (mn.2 : ℤ))) N :=
    fun N => proj_eq_tsum_upper hα hβ hb hG hev r N hz
  have hmain : Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ, modeTerm α β b mn (-z)
      * cesaro (chi α β ((r : ℤ) + (mn.2 : ℤ))) N) atTop (𝓝 (∑' _mn : ℕ × ℕ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence hb (fun mn => ?_) ?_
    · have hj : (r : ℤ) + (mn.2 : ℤ) ≠ 0 := by omega
      have hlim : Tendsto (fun N : ℕ => cesaro (chi α β ((r : ℤ) + (mn.2 : ℤ))) N) atTop (𝓝 0) :=
        tendsto_cesaro_of_ne_one (norm_chi _ _ _) (chi_ne_one hirr hj)
      have hcm := hlim.const_mul (modeTerm α β b mn (-z))
      rw [mul_zero] at hcm
      exact hcm
    · filter_upwards with N mn
      exact norm_modeTerm_mul_le hα.le hβ.le b hzneg (norm_cesaro_le (norm_chi _ _ _) N) mn
  rw [tsum_zero] at hmain
  rw [show (fun N : ℕ => proj α β r G N z)
      = fun N : ℕ => ∑' mn : ℕ × ℕ, modeTerm α β b mn (-z)
          * cesaro (chi α β ((r : ℤ) + (mn.2 : ℤ))) N from funext heq]
  exact hmain


/-! ## Step 9: the projectors are entire -/

theorem differentiable_modeTerm (α β : ℝ) (b : ℕ × ℕ → ℂ) (mn : ℕ × ℕ) :
    Differentiable ℂ (fun z => modeTerm α β b mn z) := by
  simp only [modeTerm]
  exact Differentiable.const_mul
    (Complex.differentiable_exp.comp ((differentiable_id.const_mul _).mul_const _)) _

theorem differentiable_proj {α β : ℝ} {G : ℂ → ℂ} (hG : Differentiable ℂ G) (r N : ℕ) :
    Differentiable ℂ (proj α β r G N) := by
  show Differentiable ℂ (fun z : ℂ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
      chi α β (r : ℤ) ^ k * G (z + (((k : ℝ) * per α : ℝ) : ℂ)))
  refine Differentiable.const_mul ?_ _
  have : Differentiable ℂ (fun z : ℂ => ∑ k ∈ Finset.range N,
      chi α β (r : ℤ) ^ k * G (z + (((k : ℝ) * per α : ℝ) : ℂ))) := by
    refine Differentiable.fun_sum (fun k _ => ?_)
    exact Differentiable.const_mul (hG.comp (differentiable_id.add_const _)) _
  exact this

/-! ## Step 10: the slice is holomorphic on the open lower flank -/

theorem isOpen_lowerFlank (w : ℝ) : IsOpen {z : ℂ | z.im < -w} :=
  isOpen_lt Complex.continuous_im continuous_const

theorem isOpen_upperFlank (w : ℝ) : IsOpen {z : ℂ | w < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

theorem convex_lowerFlank (w : ℝ) : Convex ℝ {z : ℂ | z.im < -w} := by
  have : {z : ℂ | z.im < -w} = {z : ℂ | Complex.imLm z < -w} := rfl
  rw [this]
  exact convex_halfSpace_lt (LinearMap.isLinear Complex.imLm) (-w)

theorem flankBound_nonneg (α β w : ℝ) (b : ℕ × ℕ → ℂ) (mn : ℕ × ℕ) :
    0 ≤ flankBound α β w b mn := by
  rw [flankBound]; positivity

theorem differentiableOn_slice {α β w : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {b : ℕ × ℕ → ℂ}
    (hb : Summable (flankBound α β w b)) (r : ℕ) :
    DifferentiableOn ℂ (slice α β b r) {z : ℂ | z.im < -w} := by
  show DifferentiableOn ℂ (fun z : ℂ => ∑' mn : ℕ × ℕ, sliceTerm α β b r mn z) _
  refine differentiableOn_tsum_of_summable_norm hb (fun mn => ?_) (isOpen_lowerFlank w)
    (fun mn y hy => ?_)
  · by_cases h : mn.2 = r
    · have he : ∀ z : ℂ, sliceTerm α β b r mn z = modeTerm α β b mn z := fun _ => if_pos h
      rw [funext he]
      exact (differentiable_modeTerm α β b mn).differentiableOn
    · have he : ∀ z : ℂ, sliceTerm α β b r mn z = 0 := fun _ => if_neg h
      rw [funext he]
      exact differentiableOn_const 0
  · by_cases h : mn.2 = r
    · have he : sliceTerm α β b r mn y = modeTerm α β b mn y := if_pos h
      rw [he]
      exact norm_modeTerm_le hα hβ b mn (le_of_lt hy)
    · have he : sliceTerm α β b r mn y = 0 := if_neg h
      rw [he, norm_zero]
      exact flankBound_nonneg α β w b mn


/-! ## Step 11: a locally bounded family on a connected open set has a holomorphic limit
as soon as it converges on one ball -/

/-- The set of points of `U` around which the family converges pointwise on a whole ball. -/
def convNbhd (F : ℕ → ℂ → ℂ) (U : Set ℂ) : Set ℂ :=
  {z | z ∈ U ∧ ∃ ρ > 0, ball z ρ ⊆ U ∧
    ∀ y ∈ ball z ρ, ∃ L : ℂ, Tendsto (fun n => F n y) atTop (𝓝 L)}

theorem isOpen_convNbhd (F : ℕ → ℂ → ℂ) (U : Set ℂ) : IsOpen (convNbhd F U) := by
  rw [Metric.isOpen_iff]
  rintro z ⟨hzU, ρ, hρ, hsub, hconv⟩
  refine ⟨ρ / 2, by linarith, fun z' hz' => ?_⟩
  have hz'sub : ball z' (ρ / 2) ⊆ ball z ρ := by
    refine Metric.ball_subset_ball' ?_
    have : dist z' z < ρ / 2 := mem_ball.mp hz'
    linarith
  exact ⟨hsub (hz'sub (mem_ball_self (by linarith))), ρ / 2, by linarith,
    hz'sub.trans hsub, fun y hy => hconv y (hz'sub hy)⟩

theorem convNbhd_closed {F : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hFd : ∀ n, DifferentiableOn ℂ (F n) U)
    (hloc : ∀ z ∈ U, ∃ ρ > 0, ball z ρ ⊆ U ∧ ∃ C : ℝ, ∀ n, ∀ y ∈ ball z ρ, ‖F n y‖ ≤ C) :
    closure (convNbhd F U) ∩ U ⊆ convNbhd F U := by
  rintro z ⟨hzcl, hzU⟩
  obtain ⟨ρ, hρ, hsub, C, hC⟩ := hloc z hzU
  obtain ⟨a, haA, hda⟩ := Metric.mem_closure_iff.mp hzcl (ρ / 12) (by linarith)
  obtain ⟨haU, ρa, hρa, hasub, haconv⟩ := haA
  set s : ℝ := min ρa (ρ / 12) with hs
  have hs0 : 0 < s := lt_min hρa (by linarith)
  have hdaz : dist a z < ρ / 12 := by rw [dist_comm]; exact hda
  have hYsub : ball a s ⊆ ball z (ρ / 3) := by
    refine Metric.ball_subset_ball' ?_
    have h1 : s ≤ ρ / 12 := min_le_right _ _
    linarith
  have hz₀ : a ∈ ball z (ρ / 3) := by
    rw [mem_ball]
    linarith
  have hacc : ∃ᶠ y in 𝓝[≠] a, y ∈ ball a s := by
    have h1 : ∀ᶠ y in 𝓝 a, y ∈ ball a s := isOpen_ball.mem_nhds (mem_ball_self hs0)
    exact (h1.filter_mono nhdsWithin_le_nhds).frequently
  have hFball : ∀ n, DifferentiableOn ℂ (F n) (ball z ρ) := fun n => (hFd n).mono hsub
  obtain ⟨g, hgdiff, hgunif⟩ :=
    GaloisForLFunctions.HTGeometry.vitali_tendstoLocallyUniformlyOn
      (c := z) (R := ρ) (C := C) (r := ρ / 3) (z₀ := a) (Y := ball a s)
      (by linarith) (by linarith) hFball hC hYsub hz₀ hacc
      (fun y hy => haconv y (Metric.ball_subset_ball (min_le_left _ _) hy))
  refine ⟨hzU, ρ / 3, by linarith, ?_, fun y hy => ⟨g y, hgunif.tendsto_at hy⟩⟩
  exact (Metric.ball_subset_ball (by linarith)).trans hsub

theorem exists_limit_of_locallyBounded {F : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hUc : IsPreconnected U) (hFd : ∀ n, DifferentiableOn ℂ (F n) U)
    (hloc : ∀ z ∈ U, ∃ ρ > 0, ball z ρ ⊆ U ∧ ∃ C : ℝ, ∀ n, ∀ y ∈ ball z ρ, ‖F n y‖ ≤ C)
    (hne : (U ∩ convNbhd F U).Nonempty) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      ∀ z ∈ U, Tendsto (fun n => F n z) atTop (𝓝 (f z)) := by
  classical
  have hAU : U ⊆ convNbhd F U :=
    hUc.subset_of_closure_inter_subset (isOpen_convNbhd F U) hne (convNbhd_closed hFd hloc)
  have hpt : ∀ z ∈ U, ∃ L : ℂ, Tendsto (fun n => F n z) atTop (𝓝 L) := by
    intro z hz
    obtain ⟨-, ρ, hρ, -, hconv⟩ := hAU hz
    exact hconv z (mem_ball_self hρ)
  refine ⟨fun z => limUnder atTop (fun n => F n z), ?_, ?_⟩
  · intro z hz
    obtain ⟨ρ, hρ, hsub, C, hC⟩ := hloc z hz
    have hFball : ∀ n, DifferentiableOn ℂ (F n) (ball z ρ) := fun n => (hFd n).mono hsub
    have hacc : ∃ᶠ y in 𝓝[≠] z, y ∈ ball z (ρ / 3) := by
      have h1 : ∀ᶠ y in 𝓝 z, y ∈ ball z (ρ / 3) :=
        isOpen_ball.mem_nhds (mem_ball_self (by linarith))
      exact (h1.filter_mono nhdsWithin_le_nhds).frequently
    obtain ⟨g, hgdiff, hgunif⟩ :=
      GaloisForLFunctions.HTGeometry.vitali_tendstoLocallyUniformlyOn
        (c := z) (R := ρ) (C := C) (r := ρ / 3) (z₀ := z) (Y := ball z (ρ / 3))
        (by linarith) (by linarith) hFball hC (subset_refl _) (mem_ball_self (by linarith))
        hacc (fun y hy => hpt y (hsub (Metric.ball_subset_ball (by linarith) hy)))
    have hfg : ∀ y ∈ ball z (ρ / 3), limUnder atTop (fun n => F n y) = g y := by
      intro y hy
      obtain ⟨L, hL⟩ := hpt y (hsub (Metric.ball_subset_ball (by linarith) hy))
      rw [hL.limUnder_eq]
      exact tendsto_nhds_unique hL (hgunif.tendsto_at hy)
    have hgAt : DifferentiableAt ℂ g z :=
      hgdiff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by linarith)))
    refine (hgAt.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show (0 : ℝ) < ρ / 3 by linarith))]
      with y hy using hfg y hy
  · intro z hz
    obtain ⟨L, hL⟩ := hpt z hz
    show Tendsto (fun n => F n z) atTop (𝓝 (limUnder atTop (fun n => F n z)))
    rw [hL.limUnder_eq]
    exact hL


/-! ## Step 12: the two flank limits admit no common holomorphic continuation -/

theorem flank_limits_incompatible {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b)) {r : ℕ}
    (hslice : ∃ z₀ : ℂ, z₀.im < -w ∧ slice α β b r z₀ ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hlow : (U ∩ {z : ℂ | z.im < -w}).Nonempty)
    (hup : (U ∩ {z : ℂ | w < z.im}).Nonempty) :
    ¬ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      (∀ y ∈ U ∩ {z : ℂ | z.im < -w}, f y = slice α β b r y) ∧
      (∀ y ∈ U ∩ {z : ℂ | w < z.im}, f y = 0) := by
  rintro ⟨f, hfdiff, hflow, hfup⟩
  obtain ⟨z₁, hz₁U, hz₁low⟩ := hlow
  obtain ⟨z₂, hz₂U, hz₂up⟩ := hup
  have hopenlow : IsOpen (U ∩ {z : ℂ | z.im < -w}) := hU.inter (isOpen_lowerFlank w)
  have hopenup : IsOpen (U ∩ {z : ℂ | w < z.im}) := hU.inter (isOpen_upperFlank w)
  have hfan : AnalyticOnNhd ℂ f U := hfdiff.analyticOnNhd hU
  have hevz : f =ᶠ[𝓝 z₂] 0 := by
    filter_upwards [hopenup.mem_nhds ⟨hz₂U, hz₂up⟩] with y hy using hfup y hy
  have hf0 : Set.EqOn f 0 U :=
    hfan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₂U hevz
  have hsl0 : ∀ y ∈ U ∩ {z : ℂ | z.im < -w}, slice α β b r y = 0 := by
    intro y hy
    have h1 : f y = 0 := by simpa using hf0 hy.1
    rw [← hflow y hy, h1]
  have hslan : AnalyticOnNhd ℂ (slice α β b r) {z : ℂ | z.im < -w} :=
    (differentiableOn_slice hα.le hβ.le hb r).analyticOnNhd (isOpen_lowerFlank w)
  have hslev : slice α β b r =ᶠ[𝓝 z₁] 0 := by
    filter_upwards [hopenlow.mem_nhds ⟨hz₁U, hz₁low⟩] with y hy using hsl0 y hy
  have hslzero : Set.EqOn (slice α β b r) 0 {z : ℂ | z.im < -w} :=
    hslan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_lowerFlank w).isPreconnected hz₁low hslev
  obtain ⟨z₀, hz₀low, hz₀ne⟩ := hslice
  exact hz₀ne (by simpa using hslzero hz₀low)

/-! ## Step 13: the projection catastrophe -/

/-- **Leaf-reflection Bohr projection catastrophe.**  For an irrational two-base one-sided flank
carrier of an even entire `G`, if the transverse `r`-slice (`r ≥ 1`) is not identically zero then
the exact-period Cesàro projectors `P_{r,N}G` are not locally bounded on any connected open set
meeting both reflected flanks. -/
theorem leaf_reflection_bohr_projection_catastrophe
    {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β) (hirr : Irrational (β / α))
    {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b))
    {G : ℂ → ℂ} (hGdiff : Differentiable ℂ G) (hev : ∀ y : ℂ, G (-y) = G y)
    (hG : ∀ y : ℂ, y.im ≤ -w → G y = ∑' mn : ℕ × ℕ, modeTerm α β b mn y)
    {r : ℕ} (hr : 1 ≤ r)
    (hslice : ∃ z₀ : ℂ, z₀.im < -w ∧ slice α β b r z₀ ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hlow : (U ∩ {z : ℂ | z.im < -w}).Nonempty)
    (hup : (U ∩ {z : ℂ | w < z.im}).Nonempty) :
    ¬ (∀ z ∈ U, ∃ ρ > 0, ball z ρ ⊆ U ∧ ∃ C : ℝ, ∀ N : ℕ, ∀ y ∈ ball z ρ,
        ‖proj α β r G N y‖ ≤ C) := by
  intro hloc
  have hFd : ∀ N : ℕ, DifferentiableOn ℂ (proj α β r G N) U :=
    fun N => (differentiable_proj hGdiff r N).differentiableOn
  obtain ⟨z₁, hz₁U, hz₁low⟩ := hlow
  have hopenlow : IsOpen (U ∩ {z : ℂ | z.im < -w}) := hU.inter (isOpen_lowerFlank w)
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.isOpen_iff.mp hopenlow z₁ ⟨hz₁U, hz₁low⟩
  have hstart : z₁ ∈ convNbhd (fun N => proj α β r G N) U := by
    refine ⟨hz₁U, ρ₁, hρ₁, hball₁.trans inter_subset_left, fun y hy => ?_⟩
    exact ⟨slice α β b r y, tendsto_proj_lower hα hβ hirr hb hG r (le_of_lt (hball₁ hy).2)⟩
  obtain ⟨f, hfdiff, hflim⟩ :=
    exists_limit_of_locallyBounded hUc hFd hloc ⟨z₁, hz₁U, hstart⟩
  refine flank_limits_incompatible hα hβ hb hslice hU hUc ⟨z₁, hz₁U, hz₁low⟩ hup
    ⟨f, hfdiff, fun y hy => ?_, fun y hy => ?_⟩
  · exact tendsto_nhds_unique (hflim y hy.1)
      (tendsto_proj_lower hα hβ hirr hb hG r (le_of_lt hy.2))
  · exact tendsto_nhds_unique (hflim y hy.1)
      (tendsto_proj_upper hα hβ hirr hb hG hev hr (le_of_lt hy.2))

/-! ## Step 14: the slice in displayed form, and its coefficient criterion -/

theorem slice_eq_tsum_row (α β : ℝ) (b : ℕ × ℕ → ℂ) (r : ℕ) (z : ℂ) :
    slice α β b r z
      = ∑' m : ℕ, b (m, r)
          * Complex.exp (-I * z * ((((m : ℝ) * α + (r : ℝ) * β : ℝ)) : ℂ)) := by
  have hinj : Function.Injective (fun m : ℕ => (m, r)) := by
    intro m₁ m₂ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).1
  have hsupp : Function.support (fun mn : ℕ × ℕ => sliceTerm α β b r mn z)
      ⊆ Set.range (fun m : ℕ => (m, r)) := by
    intro mn hmn
    have h : mn.2 = r := by
      by_contra hc
      exact hmn (if_neg hc)
    exact ⟨mn.1, by rw [← h]⟩
  rw [slice, ← hinj.tsum_eq hsupp]
  refine tsum_congr (fun m => ?_)
  have h1 : sliceTerm α β b r (m, r) z = modeTerm α β b (m, r) z := if_pos rfl
  rw [h1, modeTerm]
  rfl

/-- The `r`-row of the coefficient family, transposed so that the Cesàro extraction can be run
in the second base. -/
noncomputable def rowFamily (b : ℕ × ℕ → ℂ) (r : ℕ) : ℕ × ℕ → ℂ :=
  fun p => if p.1 = r then b (p.2, r) else 0

theorem flankBound_rowFamily_le {α β w : ℝ} (b : ℕ × ℕ → ℂ) (r : ℕ) (p : ℕ × ℕ) :
    flankBound β α w (rowFamily b r) p ≤ flankBound α β w b (p.2, p.1) := by
  by_cases h : p.1 = r
  · have h1 : rowFamily b r p = b (p.2, p.1) := by
      have : rowFamily b r p = b (p.2, r) := if_pos h
      rw [this, h]
    have h2 : freq β α p = freq α β (p.2, p.1) := by
      simp only [freq]
      ring
    rw [flankBound, flankBound, h1, h2]
  · have h1 : rowFamily b r p = 0 := if_neg h
    rw [flankBound, h1, norm_zero, zero_mul]
    exact flankBound_nonneg _ _ _ _ _

theorem summable_flankBound_rowFamily {α β w : ℝ} {b : ℕ × ℕ → ℂ}
    (hb : Summable (flankBound α β w b)) (r : ℕ) :
    Summable (flankBound β α w (rowFamily b r)) := by
  have htr : Summable (fun p : ℕ × ℕ => flankBound α β w b (p.2, p.1)) :=
    ((Equiv.prodComm ℕ ℕ).summable_iff (f := flankBound α β w b)).mpr hb
  exact Summable.of_nonneg_of_le (fun p => flankBound_nonneg _ _ _ _ _)
    (fun p => flankBound_rowFamily_le b r p) htr

theorem slice_eq_carrier_rowFamily (α β : ℝ) (b : ℕ × ℕ → ℂ) (r : ℕ) (y : ℂ) :
    slice α β b r y = ∑' p : ℕ × ℕ, modeTerm β α (rowFamily b r) p y := by
  rw [slice, ← (Equiv.prodComm ℕ ℕ).tsum_eq
    (fun p : ℕ × ℕ => modeTerm β α (rowFamily b r) p y)]
  refine tsum_congr (fun mn => ?_)
  have hcoord : (Equiv.prodComm ℕ ℕ) mn = (mn.2, mn.1) := rfl
  rw [hcoord]
  by_cases h : mn.2 = r
  · have hL : sliceTerm α β b r mn y = modeTerm α β b mn y := if_pos h
    have hR : rowFamily b r (mn.2, mn.1) = b mn := by
      have h1 : rowFamily b r (mn.2, mn.1) = b (mn.1, r) := if_pos h
      rw [h1, ← h]
    rw [hL, modeTerm, modeTerm, hR]
    congr 2
    simp only [freq]
    push_cast
    ring
  · have hL : sliceTerm α β b r mn y = 0 := if_neg h
    have hR : rowFamily b r (mn.2, mn.1) = 0 := if_neg h
    rw [hL, modeTerm, hR, zero_mul]

theorem slice_rowFamily_eq (α β : ℝ) (b : ℕ × ℕ → ℂ) (r m₀ : ℕ) (z : ℂ) :
    slice β α (rowFamily b r) m₀ z = modeTerm α β b (m₀, r) z := by
  rw [slice, tsum_eq_single (r, m₀)]
  · have h1 : sliceTerm β α (rowFamily b r) m₀ (r, m₀) z
        = modeTerm β α (rowFamily b r) (r, m₀) z := if_pos rfl
    have h2 : rowFamily b r (r, m₀) = b (m₀, r) := if_pos rfl
    rw [h1, modeTerm, modeTerm, h2]
    congr 2
    simp only [freq]
    push_cast
    ring
  · intro p hp
    by_cases h : p.2 = m₀
    · have h1 : sliceTerm β α (rowFamily b r) m₀ p z
          = modeTerm β α (rowFamily b r) p z := if_pos h
      have hp1 : p.1 ≠ r := by
        intro hc
        exact hp (Prod.ext hc h)
      have h2 : rowFamily b r p = 0 := if_neg hp1
      rw [h1, modeTerm, h2, zero_mul]
    · exact if_neg h

/-- **Coefficient criterion.**  A single nonzero coefficient in the `r`-row makes the slice
`B_r` nonzero on the open lower flank: the Cesàro extraction in the second base recovers each
coefficient. -/
theorem slice_ne_zero_of_coeff_ne_zero {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (β / α)) {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b))
    {r m₀ : ℕ} (hcoeff : b (m₀, r) ≠ 0) :
    ∃ z₀ : ℂ, z₀.im < -w ∧ slice α β b r z₀ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hirr' : Irrational (α / β) := by
    have h := Irrational.inv hirr
    rwa [inv_div] at h
  set z : ℂ := Complex.I * (-(w + 1) : ℝ) with hzdef
  have hzim : z.im = -(w + 1) := by simp [hzdef]
  have hzlt : z.im < -w := by rw [hzim]; linarith
  have hzle : z.im ≤ -w := le_of_lt hzlt
  have hzero : ∀ (k : ℕ), slice α β b r (z + (((k : ℝ) * per β : ℝ) : ℂ)) = 0 := by
    intro k
    refine hcon _ ?_
    have : (z + (((k : ℝ) * per β : ℝ) : ℂ)).im = z.im := by simp
    rw [this]
    exact hzlt
  have hlim := tendsto_proj_lower (α := β) (β := α) hβ hα hirr'
    (summable_flankBound_rowFamily hb r)
    (fun y _ => slice_eq_carrier_rowFamily α β b r y) m₀ hzle
  have hzeroN : ∀ N : ℕ, proj β α m₀ (slice α β b r) N z = 0 := by
    intro N
    rw [proj]
    have : ∀ k ∈ Finset.range N, chi β α (m₀ : ℤ) ^ k
        * slice α β b r (z + (((k : ℝ) * per β : ℝ) : ℂ)) = 0 := by
      intro k _
      rw [hzero k, mul_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero, mul_zero]
  have hlim0 : Tendsto (fun N : ℕ => proj β α m₀ (slice α β b r) N z) atTop (𝓝 0) := by
    rw [show (fun N : ℕ => proj β α m₀ (slice α β b r) N z) = fun _ : ℕ => (0 : ℂ) from
      funext hzeroN]
    exact tendsto_const_nhds
  have heq0 : slice β α (rowFamily b r) m₀ z = 0 := tendsto_nhds_unique hlim hlim0
  rw [slice_rowFamily_eq, modeTerm] at heq0
  rcases mul_eq_zero.mp heq0 with h | h
  · exact hcoeff h
  · exact Complex.exp_ne_zero _ h

/-! ## Step 15: the card's theorem in coefficient form -/

/-- **Leaf-reflection Bohr projection catastrophe, coefficient form.**  A single nonzero
transverse coefficient `b_{m₀,r}` with `r ≥ 1` already forces the exact-period Cesàro projectors
to be nonnormal on every connected open set joining the two reflected flanks. -/
theorem leaf_reflection_catastrophe_of_coeff
    {α β w : ℝ} (hα : 0 < α) (hβ : 0 < β) (hirr : Irrational (β / α))
    {b : ℕ × ℕ → ℂ} (hb : Summable (flankBound α β w b))
    {G : ℂ → ℂ} (hGdiff : Differentiable ℂ G) (hev : ∀ y : ℂ, G (-y) = G y)
    (hG : ∀ y : ℂ, y.im ≤ -w → G y = ∑' mn : ℕ × ℕ, modeTerm α β b mn y)
    {r m₀ : ℕ} (hr : 1 ≤ r) (hcoeff : b (m₀, r) ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hlow : (U ∩ {z : ℂ | z.im < -w}).Nonempty)
    (hup : (U ∩ {z : ℂ | w < z.im}).Nonempty) :
    ¬ (∀ z ∈ U, ∃ ρ > 0, ball z ρ ⊆ U ∧ ∃ C : ℝ, ∀ N : ℕ, ∀ y ∈ ball z ρ,
        ‖proj α β r G N y‖ ≤ C) :=
  leaf_reflection_bohr_projection_catastrophe hα hβ hirr hb hGdiff hev hG hr
    (slice_ne_zero_of_coeff_ne_zero hα hβ hirr hb hcoeff) hU hUc hlow hup


end

end GaloisForLFunctions.LeafReflectionProjection
