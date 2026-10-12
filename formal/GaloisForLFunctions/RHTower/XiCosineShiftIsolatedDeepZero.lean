import GaloisForLFunctions.RHTower.XiCosineShiftCrowdedPersistence
import GaloisForLFunctions.RHTower.XiHeatMomentSmallTimePositivity
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder

/-!
# Isolated deep zeros of `ξ` survive the cosine producer at large height

Let `ρ₀` be a zero of `ξ` at height `γ₀` and depth `δ = ½ − Re ρ₀` (spectral point
`ζ₀ = γ₀ + iδ` of `Ξ`). Fix margins `h, r, s₀ > 0` and a multiplicity bound `M`.

**Theorem** (`exists_nonreal_zero_cosShiftXi_of_isolated`). There are `L` and `T₀`, depending only on
`h, r, s₀, M`, with the following property. Suppose that `γ₀ ≥ T₀`, that `η := δ − h − r − s₀ ≥ 0`,
that `ζ₀` and `ζ̄₀` have multiplicity at most `M`, and that every other zero with ordinate within `L`
of `γ₀` has `|Im| ≤ η`. Then `cos(hD)Ξ` has a nonreal zero.

So at large height an isolated deep zero is never absorbed by the cosine producer before the
depth `h` reaches its own depth minus `r + s₀`. The real-rootedness threshold of the cosine
ladder is therefore bounded below by the depth of every isolated deep zero at large height, up to
arbitrarily small margins.

**Proof.** Apply the exceptional-set persistence law
(`exists_zero_cosShiftXi_of_exceptionalSet`). Its inputs are the following.
* **Neighbours.** By Riemann–von Mangoldt with the `O(log T)` remainder, a window of half-width `H`
  around `γ₀` carries at least `(H/π)log((γ₀ − H)/2π) − 2C log(γ₀ + H)` zero copies. All but `2M`
  of them are shallow (`|Im| ≤ η`) by isolation.
* **Far deep copies.** Each copy changes the modulus ratio across the shift by at most
  `exp(h/(d − r)²)`, where `d ≥ L` is its horizontal distance. Since `(d − r)² ≥ (L² + d²)/8`, the
  total is at most `exp(8h Σ_ρ 1/(L² + (γ₀ − γ)²)) ≤ exp((64h/L)(C' + log(L + γ₀ + 4)))`, by the width-`L`
  Lorentzian mass.
* **Copies at `ζ₀`.** Each contributes at most `(2h + r)/r`.

The neighbour gain grows like `κ(H/π − 2C) log γ₀`, while the far loss grows like `(64h/L) log γ₀`.
For `L` large the gain wins, and `T₀` absorbs the constants.
-/

open Complex ComplexConjugate Filter Topology Set Polynomial Metric

namespace RHTower.CosineIsolatedDeepZero

open GaloisForLFunctions.HTGeometry RHTower.DeBruijn RHTower.CosineDefectBudget
  RHTower.CrowdedPersistence RHTower.CosineCrowdedPersistence

noncomputable section

/-! ## Riemann–von Mangoldt in windows -/

theorem mul_log_sub_mul_log_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * (Real.log a + 1) ≤ b * Real.log b - a * Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h1
  have h2 : b * (1 - a / b) ≤ b * (Real.log b - Real.log a) := mul_le_mul_of_nonneg_left h1 hb.le
  rw [mul_sub, mul_div_cancel₀ _ hb.ne', mul_one] at h2
  nlinarith

/-- Every window `(T − H, T + H]` with `T − H ≥ T₁` carries a finite set of zero copies of size at
least `(H/π)(log(T − H) − log 2π) − 2C log(T + H)`. -/
def WindowLowerCount (C T₁ : ℝ) : Prop :=
  ∀ T H : ℝ, 0 ≤ H → T₁ ≤ T - H →
    ∃ P : Finset XiZeroCopy,
      (∀ q ∈ P, T - H < xiCopyOrdinate q ∧ xiCopyOrdinate q ≤ T + H) ∧
      H / Real.pi * (Real.log (T - H) - Real.log (2 * Real.pi)) - 2 * C * Real.log (T + H) ≤
        P.card

/-- **Window lower count**, from Riemann–von Mangoldt with the `O(log T)` remainder. -/
theorem exists_window_lower_count :
    ∃ C T₁ : ℝ, 0 < C ∧ 4 ≤ T₁ ∧ WindowLowerCount C T₁ := by
  obtain ⟨C, hC, T₁, hT₁, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨C, T₁, hC, hT₁, fun T H hH hTH => ?_⟩
  have ha : 0 < T - H := by linarith
  obtain ⟨P, hP, hcard⟩ := exists_finset_xiZeroCopy_window (T := T) (h := H) ha.le hH
  refine ⟨P, hP, le_trans ?_ hcard⟩
  have h1 := hrem (T + H) (by linarith)
  have h2 := hrem (T - H) hTH
  have hsub := routeKSmoothRVMCount_sub_eq ha (by linarith : 0 < T + H)
  have hconv := mul_log_sub_mul_log_ge ha (by linarith : T - H ≤ T + H)
  have hbase : Real.log routeKRVMBase = Real.log (2 * Real.pi) + 1 := by
    rw [routeKRVMBase, Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  have hlog : Real.log (T - H) ≤ Real.log (T + H) :=
    Real.log_le_log ha (by linarith)
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [abs_le] at h1 h2
  have hmain : H / Real.pi * (Real.log (T - H) - Real.log (2 * Real.pi)) ≤
      routeKSmoothRVMCount (T + H) - routeKSmoothRVMCount (T - H) := by
    rw [hsub, hbase, le_div_iff₀ hpi]
    have e : H / Real.pi * (Real.log (T - H) - Real.log (2 * Real.pi)) * (2 * Real.pi) =
        (T + H - (T - H)) * (Real.log (T - H) + 1 - (Real.log (2 * Real.pi) + 1)) := by
      field_simp
      ring
    rw [e]
    nlinarith
  nlinarith

/-! ## The modulus ratio of a single copy across the shift -/

/-- **A copy at the centre.** On the circle `|z − (ζ₀ − ih)| = r` the copy at `ζ₀` changes the
modulus by at most `(2h + r)/r`. -/
theorem norm_shift_le_centre {z ζ₀ : ℂ} {h r : ℝ} (hh : 0 ≤ h) (hr : 0 < r)
    (hz : ‖z - (ζ₀ - h * I)‖ = r) :
    ‖z - h * I - ζ₀‖ ≤ (2 * h + r) / r * ‖z + h * I - ζ₀‖ ∧ 0 < ‖z + h * I - ζ₀‖ := by
  have e1 : z + h * I - ζ₀ = z - (ζ₀ - h * I) := by ring
  have e2 : z - h * I - ζ₀ = (z - (ζ₀ - h * I)) - (2 * h : ℝ) * I := by push_cast; ring
  have hI : ‖((2 * h : ℝ) : ℂ) * I‖ = 2 * h := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [e1, hz, e2]
  refine ⟨?_, hr⟩
  rw [div_mul_cancel₀ _ hr.ne']
  calc ‖(z - (ζ₀ - h * I)) - ((2 * h : ℝ) : ℂ) * I‖
      ≤ ‖z - (ζ₀ - h * I)‖ + ‖((2 * h : ℝ) : ℂ) * I‖ := norm_sub_le _ _
    _ = 2 * h + r := by rw [hz, hI]; ring

/-- **A far copy.** On the disc `|z − (ζ₀ − ih)| ≤ r` in the upper half-plane, a copy `ζ` with
`Im ζ ≤ ½` at horizontal distance `d ≥ L ≥ 2r` from `ζ₀` changes the modulus by at most
`exp(8h/(L² + d²))`. -/
theorem norm_shift_le_far {z ζ ζ₀ : ℂ} {h r L : ℝ} (hh : 0 ≤ h) (hr : 0 ≤ r)
    (hz : ‖z - (ζ₀ - h * I)‖ ≤ r) (hzim : 0 ≤ z.im) (hζ : ζ.im ≤ 1 / 2) (hL : 2 * r ≤ L)
    (hL0 : 0 < L) (hd : L ≤ |ζ.re - ζ₀.re|) :
    ‖z - h * I - ζ‖ ≤ Real.exp (8 * h * (1 / (L ^ 2 + (ζ₀.re - ζ.re) ^ 2))) * ‖z + h * I - ζ‖ ∧
      0 < ‖z + h * I - ζ‖ := by
  set d := |ζ.re - ζ₀.re| with hd_def
  have hre : |z.re - ζ₀.re| ≤ r := by
    have := Complex.abs_re_le_norm (z - (ζ₀ - h * I))
    simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero] at this
    linarith
  have hb : d / 2 ≤ ‖z + h * I - ζ‖ := by
    have h1 := Complex.abs_re_le_norm (z + h * I - ζ)
    simp only [sub_re, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_zero] at h1
    have h2 : d ≤ |z.re - ζ.re| + |z.re - ζ₀.re| := by
      rw [hd_def]
      calc |ζ.re - ζ₀.re| = |(z.re - ζ₀.re) - (z.re - ζ.re)| := by ring_nf
        _ ≤ |z.re - ζ₀.re| + |z.re - ζ.re| := abs_sub _ _
        _ = _ := add_comm _ _
    linarith
  have hd0 : 0 < d := lt_of_lt_of_le hL0 hd
  have hbpos : 0 < ‖z + h * I - ζ‖ := by linarith
  refine ⟨?_, hbpos⟩
  set b := ‖z + h * I - ζ‖ with hb_def
  have hsq : (ζ₀.re - ζ.re) ^ 2 = d ^ 2 := by rw [hd_def, sq_abs]; ring
  rw [hsq]
  set w := 1 / (L ^ 2 + d ^ 2) with hw
  have hLd : 0 < L ^ 2 + d ^ 2 := by positivity
  have hb2 : (L ^ 2 + d ^ 2) / 8 ≤ b ^ 2 := by nlinarith
  have hwL : w * (L ^ 2 + d ^ 2) = 1 := by rw [hw]; field_simp
  have ha2 : ‖z - h * I - ζ‖ ^ 2 ≤ b ^ 2 + 2 * h := by
    rw [norm_sub_sq_shift]
    nlinarith
  have hw0 : 0 ≤ w := by positivity
  have hexp : b ^ 2 + 2 * h ≤ (Real.exp (8 * h * w) * b) ^ 2 := by
    have e : (Real.exp (8 * h * w) * b) ^ 2 = Real.exp (16 * h * w) * b ^ 2 := by
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; ring_nf
    rw [e]
    have h1 := Real.add_one_le_exp (16 * h * w)
    have h2 : 2 * h ≤ 16 * h * w * b ^ 2 := by
      have : 16 * h * w * ((L ^ 2 + d ^ 2) / 8) = 2 * h := by
        rw [show 16 * h * w * ((L ^ 2 + d ^ 2) / 8) = 2 * h * (w * (L ^ 2 + d ^ 2)) by ring, hwL,
          mul_one]
      rw [← this]
      exact mul_le_mul_of_nonneg_left hb2 (by positivity)
    nlinarith [sq_nonneg b]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (ha2.trans hexp)

/-! ## The exceptional product -/

theorem lorentzMassWTerm_eq (L : ℝ) (q₀ q : XiZeroCopy) :
    lorentzMassWTerm L (xiSpectralPoint q₀).re q =
      1 / (L ^ 2 + ((xiSpectralPoint q₀).re - (xiSpectralPoint q).re) ^ 2) := by
  rw [lorentzMassWTerm, xiSpectralPoint_re_eq_ordinate q, xiCopyOrdinate]

/-- **The exceptional product.** Let every copy of horizontal distance at most `L` from `ζ₀` either
sit at `ζ₀` or `ζ̄₀`, or have `|Im| ≤ η`, and let at most `M` copies sit at `ζ₀` or `ζ̄₀`. Then any
finite family of copies with `Im > η` changes the modulus across the shift by at most
`((2h + r)/r)^M · exp(8h Σ_ρ 1/(L² + (γ₀ − γ)²))`. -/
theorem prod_shift_le_of_isolated {q₀ : XiZeroCopy} {η h r L : ℝ} {M : ℕ} (hh : 0 ≤ h)
    (hr : 0 < r) (hL : 2 * r ≤ L) (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hζ₀ : 0 ≤ (xiSpectralPoint q₀).im)
    (hmult : ∀ G : Finset XiZeroCopy, (∀ q ∈ G, xiSpectralPoint q = xiSpectralPoint q₀ ∨
      xiSpectralPoint q = conj (xiSpectralPoint q₀)) → G.card ≤ M)
    (hiso : ∀ q, |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L →
      xiSpectralPoint q ≠ xiSpectralPoint q₀ → xiSpectralPoint q ≠ conj (xiSpectralPoint q₀) →
      |(xiSpectralPoint q).im| ≤ η)
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, η < (xiSpectralPoint q).im) {z : ℂ}
    (hz : ‖z - (xiSpectralPoint q₀ - h * I)‖ = r) (hzim : 0 ≤ z.im) :
    (F.val.map fun q => ‖z - h * I - xiSpectralPoint q‖).prod ≤
        ((2 * h + r) / r) ^ M * Real.exp (8 * h * lorentzMassW L (xiSpectralPoint q₀).re) *
          (F.val.map fun q => ‖z + h * I - xiSpectralPoint q‖).prod ∧
      ∀ q ∈ F, z + h * I ≠ xiSpectralPoint q := by
  classical
  set ζ₀ := xiSpectralPoint q₀ with hζ₀_def
  set c := (2 * h + r) / r with hc
  have hc1 : 1 ≤ c := by rw [hc, le_div_iff₀ hr]; linarith
  have hL0 : 0 < L := by linarith
  set f : XiZeroCopy → ℝ := fun q =>
    if xiSpectralPoint q = ζ₀ then c else Real.exp (8 * h * lorentzMassWTerm L ζ₀.re q) with hf
  have hone : ∀ q ∈ F, ‖z - h * I - xiSpectralPoint q‖ ≤ f q * ‖z + h * I - xiSpectralPoint q‖ ∧
      0 < ‖z + h * I - xiSpectralPoint q‖ := by
    intro q hq
    by_cases hnear : xiSpectralPoint q = ζ₀
    · simp only [hf, hnear, if_true]
      exact norm_shift_le_centre hh hr hz
    · simp only [hf, hnear, if_false]
      have hfar : L ≤ |(xiSpectralPoint q).re - ζ₀.re| := by
        by_contra hlt
        rw [not_le] at hlt
        have hconj : xiSpectralPoint q ≠ conj ζ₀ := by
          intro hc'
          have := hF q hq
          rw [hc', Complex.conj_im] at this
          linarith
        have := hiso q hlt.le hnear hconj
        have := hF q hq
        rw [abs_le] at *
        linarith
      rw [lorentzMassWTerm_eq]
      exact norm_shift_le_far hh hr.le hz.le hzim
        ((le_abs_self _).trans (abs_xiSpectralPoint_im_le q)) hL hL0 hfar
  refine ⟨?_, fun q hq h0 => by
    have := (hone q hq).2
    rw [h0, sub_self, norm_zero] at this
    exact lt_irrefl _ this⟩
  rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod]
  have h1 : ∏ q ∈ F, ‖z - h * I - xiSpectralPoint q‖ ≤
      (∏ q ∈ F, f q) * ∏ q ∈ F, ‖z + h * I - xiSpectralPoint q‖ := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => (hone q hq).1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun q _ => norm_nonneg _))
  rw [hf, Finset.prod_ite, Finset.prod_const]
  apply mul_le_mul
  · refine pow_le_pow_right₀ hc1 (hmult _ fun q hq => Or.inl (Finset.mem_filter.mp hq).2)
  · rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (summable_lorentzMassWTerm hL1 _).sum_le_tsum _
      fun q _ => lorentzMassWTerm_nonneg hL1 _ q
  · exact Finset.prod_nonneg fun q _ => (Real.exp_pos _).le
  · positivity

/-! ## The growth comparison -/

/-- The exponent bookkeeping: the neighbour gain `(κ/2)·N` beats the centre and far losses
`D + u(C' + log(L + γ₀ + 4))` once `log(γ₀ − H)` is large. Here `ip` stands for `1/π`. -/
theorem crowd_exponent_neg {D u Cp lL lG l3 lp ℓ κ C N P M ip : ℝ} (hκ : 0 < κ) (hip : 0 < ip)
    (hC : 0 ≤ C) (hu0 : 0 ≤ u) (hu : u ≤ κ * ip / 4) (hℓ0 : 0 ≤ ℓ) (hN : P - M ≤ N)
    (hP : (2 * C + ip) * (ℓ - lp) - 2 * C * lG ≤ P) (hG : lG ≤ l3 + ℓ) (hLL : lL ≤ l3 + ℓ)
    (hℓ : D + u * (Cp + l3) + κ / 2 * ((2 * C + ip) * lp + 2 * C * l3 + M) + κ * ip / 4 ≤
      κ * ip / 4 * ℓ) :
    D + u * (Cp + lL) - κ / 2 * N < 0 := by
  have h1 := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ κ / 2)
  have h2 := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ κ / 2)
  have h3 := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ κ * C)
  have h4 := mul_le_mul_of_nonneg_left hLL hu0
  have h5 := mul_le_mul_of_nonneg_right hu hℓ0
  have h6 : 0 < κ * ip := mul_pos hκ hip
  nlinarith

/-- The crowding constant is bounded below uniformly in the depth: with `η + h + r + s₀ ≤ Im ζ₀ ≤ ½`
it is at least `4hs₀/((H + r)² + (1 + r)²)`. -/
theorem crowdKappa_ge {ζ₀ : ℂ} {h r η H s₀ : ℝ} (hh : 0 ≤ h) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (hs₀ : 0 < s₀) (hd : η + h + r + s₀ ≤ ζ₀.im) (hδ : ζ₀.im ≤ 1 / 2) :
    4 * h * s₀ / ((H + r) ^ 2 + (1 + r) ^ 2) ≤ crowdKappa ζ₀ h r η H := by
  rw [crowdKappa]
  have h1 : 0 < ζ₀.im + r + η := by linarith
  have h2 : ζ₀.im + r + η ≤ 1 + r := by linarith
  apply div_le_div₀ (mul_nonneg (by positivity) (by linarith))
    (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)
  exact add_le_add_right (pow_le_pow_left₀ h1.le h2 2) _

/-! ## Isolated deep zeros at large height -/

/-- The window half-width `H = 2πC + 1` of the neighbour count. -/
def isoH (C : ℝ) : ℝ := 2 * Real.pi * C + 1

/-- The uniform crowding constant `4hs₀/((H + r)² + (1 + r)²)`. -/
def isoKappa (C h r s₀ : ℝ) : ℝ := 4 * h * s₀ / ((isoH C + r) ^ 2 + (1 + r) ^ 2)

/-- The isolation window `H + 2r + 1 + 256πh/κ`. -/
def isoL (C h r s₀ : ℝ) : ℝ := isoH C + 2 * r + 1 + 256 * h / (isoKappa C h r s₀ * Real.pi⁻¹)

/-- The constant term of the growth comparison. -/
def isoA (C h r s₀ : ℝ) (M : ℕ) : ℝ :=
  ((M : ℝ) + 1) * Real.log ((2 * h + r) / r) +
    64 * h / isoL C h r s₀ * (xiLineTwoLogDerivConstant + Real.log 3) +
    isoKappa C h r s₀ / 2 * ((2 * C + Real.pi⁻¹) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M) +
    isoKappa C h r s₀ * Real.pi⁻¹ / 4

/-- The threshold height `T₁ + L + 4 + 4H + exp(4πA/κ)`. -/
def isoT (C T₁ h r s₀ : ℝ) (M : ℕ) : ℝ :=
  T₁ + isoL C h r s₀ + 4 + 4 * isoH C +
    Real.exp (isoA C h r s₀ M / (isoKappa C h r s₀ * Real.pi⁻¹ / 4))

theorem isoKappa_pos {C h r s₀ : ℝ} (hC : 0 < C) (hh : 0 < h) (hr : 0 ≤ r) (hs₀ : 0 < s₀) :
    0 < isoKappa C h r s₀ := by
  rw [isoKappa, isoH]; positivity

theorem isoL_pos {C h r s₀ : ℝ} (hC : 0 < C) (hh : 0 < h) (hr : 0 < r) (hs₀ : 0 < s₀) :
    0 < isoL C h r s₀ := by
  have := isoKappa_pos hC hh hr.le hs₀
  rw [isoL, isoH]; positivity

/-- **Isolated deep zeros, explicit form.** Given the window count with constants `C, T₁`, the
conclusion of `exists_zero_cosShiftXi_of_isolated` holds with the window `isoL C h r s₀` and the
height `isoT C T₁ h r s₀ M`. -/
theorem exists_zero_cosShiftXi_of_isolated_explicit {C T₁ : ℝ} (hC : 0 < C) (hT₁ : 4 ≤ T₁)
    (hwin : WindowLowerCount C T₁) {h r s₀ : ℝ} (hh : 0 < h) (hr : 0 < r) (hs₀ : 0 < s₀)
    (M : ℕ) (q₀ : XiZeroCopy) (η : ℝ) (hη : 0 ≤ η)
    (hdepth : η + h + r + s₀ ≤ (xiSpectralPoint q₀).im)
    (hT : isoT C T₁ h r s₀ M ≤ (xiSpectralPoint q₀).re)
    (hmult : ∀ G : Finset XiZeroCopy, (∀ q ∈ G, xiSpectralPoint q = xiSpectralPoint q₀ ∨
      xiSpectralPoint q = conj (xiSpectralPoint q₀)) → G.card ≤ M)
    (hiso : ∀ q, |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ isoL C h r s₀ →
      xiSpectralPoint q ≠ xiSpectralPoint q₀ → xiSpectralPoint q ≠ conj (xiSpectralPoint q₀) →
      |(xiSpectralPoint q).im| ≤ η) :
    ∃ z, ‖z - (xiSpectralPoint q₀ - h * I)‖ ≤ r ∧ η < z.im ∧ cosShiftXi h z = 0 := by
  classical
  have hpi := Real.pi_pos
  set ip := Real.pi⁻¹ with hip_def
  have hip : 0 < ip := inv_pos.mpr hpi
  set H := isoH C with hH
  have hH0 : 0 < H := by rw [hH, isoH]; positivity
  have hHpi : H / Real.pi = 2 * C + ip := by rw [hH, isoH, hip_def]; field_simp
  set κ₀ := isoKappa C h r s₀ with hκ₀
  have hκ₀0 : 0 < κ₀ := isoKappa_pos hC hh hr.le hs₀
  set L := isoL C h r s₀ with hL
  have hpos : 0 ≤ 256 * h / (κ₀ * ip) := by positivity
  have hLeq : L = H + 2 * r + 1 + 256 * h / (κ₀ * ip) := rfl
  have hhL : 256 * h / (κ₀ * ip) ≤ L := by rw [hLeq]; linarith
  have hL1 : 1 ≤ L := by rw [hLeq]; linarith
  have hL0 : 0 < L := by linarith
  have h2rL : 2 * r ≤ L := by rw [hLeq]; linarith
  have hHL : H ≤ L := by rw [hLeq]; linarith
  set u := 64 * h / L with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hu : u ≤ κ₀ * ip / 4 := by
    rw [hu_def, div_le_iff₀ hL0]
    have h1 := mul_le_mul_of_nonneg_left hhL (by positivity : (0 : ℝ) ≤ κ₀ * ip / 4)
    have h2 : κ₀ * ip / 4 * (256 * h / (κ₀ * ip)) = 64 * h := by field_simp; ring
    linarith
  set c := (2 * h + r) / r with hc
  have hc0 : 0 < c := by positivity
  set D := ((M : ℝ) + 1) * Real.log c with hD
  set Cp := xiLineTwoLogDerivConstant
  set A := isoA C h r s₀ M with hA_def
  have hA : A = D + u * (Cp + Real.log 3) +
      κ₀ / 2 * ((2 * C + ip) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M) + κ₀ * ip / 4 :=
    rfl
  have hTeq : isoT C T₁ h r s₀ M = T₁ + L + 4 + 4 * H + Real.exp (A / (κ₀ * ip / 4)) := rfl
  rw [hTeq] at hT
  set ζ₀ := xiSpectralPoint q₀ with hζ₀_def
  set γ₀ := ζ₀.re with hγ₀
  have hexp0 := Real.exp_pos (A / (κ₀ * ip / 4))
  have hγH : T₁ ≤ γ₀ - H := by linarith
  have hγpos : 0 < γ₀ - H := by linarith
  have hγ0 : 0 < γ₀ := by linarith
  have hδ : ζ₀.im ≤ 1 / 2 := (le_abs_self _).trans (abs_xiSpectralPoint_im_le q₀)
  -- the window of neighbours
  obtain ⟨P, hPwin, hPcard⟩ := hwin γ₀ H hH0.le hγH
  set bad : XiZeroCopy → Prop := fun q => xiSpectralPoint q = ζ₀ ∨ xiSpectralPoint q = conj ζ₀
    with hbad
  set Nb := P.filter fun q => ¬ bad q with hNb_def
  have hNcard : (P.card : ℝ) - M ≤ Nb.card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := P) bad
    have hb : (P.filter bad).card ≤ M := hmult _ fun q hq => (Finset.mem_filter.mp hq).2
    have : P.card ≤ M + Nb.card := by rw [hNb_def]; omega
    have : (P.card : ℝ) ≤ M + Nb.card := by exact_mod_cast this
    linarith
  have hPre : ∀ q ∈ P, |(xiSpectralPoint q).re - γ₀| ≤ H := by
    intro q hq
    obtain ⟨h1, h2⟩ := hPwin q hq
    rw [xiSpectralPoint_re_eq_ordinate, abs_le]
    constructor <;> linarith
  -- the exceptional set
  set Exc : Set XiZeroCopy := {q | q ≠ q₀ ∧ η < (xiSpectralPoint q).im} with hExc
  have hzim : ∀ z ∈ sphere (ζ₀ - h * I) r, 0 ≤ z.im := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have h1 := Complex.abs_im_le_norm (z - (ζ₀ - h * I))
    rw [hz] at h1
    have e : (z - (ζ₀ - h * I)).im = z.im - (ζ₀.im - h) := by simp
    rw [e, abs_le] at h1
    linarith
  set B := c ^ M * Real.exp (8 * h * lorentzMassW L γ₀) with hB
  have hprod := fun (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, q ∈ Exc) (z : ℂ)
      (hz : z ∈ sphere (ζ₀ - h * I) r) =>
    prod_shift_le_of_isolated (M := M) (L := L) (η := η) hh.le hr h2rL hL1 hη (by linarith)
      hmult hiso F (fun q hq => (hF q hq).2) (by rwa [mem_sphere, dist_eq_norm] at hz)
      (hzim z hz)
  have hB0 : 0 ≤ B := by positivity
  refine exists_zero_cosShiftXi_of_exceptionalSet (Exc := Exc) (Nb := Nb) (H := H) (B := B) hh hr
    hη hB0 (by linarith) (fun h' => h'.1 rfl) (fun q hq hq' => by
      by_contra hlt
      exact hq' ⟨hq, not_le.mp hlt⟩)
    (fun q hq z hz => (hprod {q} (by simpa using hq) z hz).2 q (Finset.mem_singleton_self q))
    (fun F hF z hz => (hprod F hF z hz).1) ?_ ?_
  · intro q hq
    obtain ⟨hqP, hqb⟩ := Finset.mem_filter.mp hq
    have hre := hPre q hqP
    have hne1 : xiSpectralPoint q ≠ ζ₀ := fun h' => hqb (Or.inl h')
    have hne2 : xiSpectralPoint q ≠ conj ζ₀ := fun h' => hqb (Or.inr h')
    have him := hiso q (hre.trans hHL) hne1 hne2
    rw [abs_le] at him
    refine ⟨fun h' => hne1 (by rw [h']), fun h' => ?_, hre, him.1⟩
    exact absurd him.2 (not_le.mpr h'.2)
  · -- the growth comparison
    have hκ : κ₀ ≤ crowdKappa ζ₀ h r η H :=
      crowdKappa_ge hh.le hr.le hη hs₀ (by linarith) hδ
    have hsq : Real.sqrt (1 - crowdKappa ζ₀ h r η H) ≤ Real.exp (-κ₀ / 2) := by
      have h1 : 1 - crowdKappa ζ₀ h r η H ≤ Real.exp (-κ₀) := by
        have := Real.add_one_le_exp (-κ₀)
        linarith
      have h2 : Real.exp (-κ₀) = Real.exp (-κ₀ / 2) ^ 2 := by
        rw [sq, ← Real.exp_add]; ring_nf
      calc Real.sqrt (1 - crowdKappa ζ₀ h r η H) ≤ Real.sqrt (Real.exp (-κ₀)) :=
            Real.sqrt_le_sqrt h1
        _ = Real.exp (-κ₀ / 2) := by rw [h2, Real.sqrt_sq (Real.exp_pos _).le]
    have hpow : Real.sqrt (1 - crowdKappa ζ₀ h r η H) ^ Nb.card ≤
        Real.exp ((Nb.card : ℝ) * (-κ₀ / 2)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq _
    have hmass := lorentzMassW_le_log hL1 γ₀
    rw [abs_of_pos hγ0] at hmass
    have hcpow : c * c ^ M = Real.exp D := by
      rw [hD, show ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
        Real.exp_log hc0, pow_succ]
      ring
    set lL := Real.log (L + γ₀ + 4)
    set ℓ := Real.log (γ₀ - H) with hℓ_def
    have hℓbig : A / (κ₀ * ip / 4) ≤ ℓ := by
      rw [hℓ_def, Real.le_log_iff_exp_le hγpos]
      linarith
    have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
    have hl3 : Real.log 3 + ℓ = Real.log (3 * (γ₀ - H)) := by
      rw [Real.log_mul (by norm_num) hγpos.ne']
    have hG : Real.log (γ₀ + H) ≤ Real.log 3 + ℓ := by
      rw [hl3]; exact Real.log_le_log (by linarith) (by linarith)
    have hLL : lL ≤ Real.log 3 + ℓ := by
      rw [hl3]; exact Real.log_le_log (by linarith) (by linarith)
    have hPc : (2 * C + ip) * (ℓ - Real.log (2 * Real.pi)) - 2 * C * Real.log (γ₀ + H) ≤
        P.card := by
      rw [← hHpi]; exact hPcard
    have hℓA : A ≤ κ₀ * ip / 4 * ℓ := by
      have h1 := mul_le_mul_of_nonneg_left hℓbig (by positivity : (0 : ℝ) ≤ κ₀ * ip / 4)
      rwa [mul_div_cancel₀ _ (by positivity : κ₀ * ip / 4 ≠ 0)] at h1
    have hE := crowd_exponent_neg (D := D) (Cp := Cp) (lL := lL) hκ₀0 hip hC.le hu0 hu hℓ0
      hNcard hPc hG hLL (by rw [hA] at hℓA; linarith)
    have hmass' : 8 * h * lorentzMassW L γ₀ ≤ u * (Cp + lL) := by
      have := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ 8 * h)
      have e : 8 * h * (8 / L * (Cp + Real.log (L + γ₀ + 4))) = u * (Cp + lL) := by
        rw [hu_def]; field_simp; ring
      linarith
    calc (2 * h + r) / r * B * Real.sqrt (1 - crowdKappa ζ₀ h r η H) ^ Nb.card
        ≤ (c * c ^ M) * Real.exp (8 * h * lorentzMassW L γ₀) *
            Real.exp ((Nb.card : ℝ) * (-κ₀ / 2)) := by
          rw [hB, ← hc, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = Real.exp (D + 8 * h * lorentzMassW L γ₀ - κ₀ / 2 * Nb.card) := by
          rw [hcpow, ← Real.exp_add, ← Real.exp_add]; ring_nf
      _ < 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by linarith)

/-- **Isolated deep zeros survive the cosine producer at large height.** For margins `h, r, s₀ > 0`
and a multiplicity bound `M` there are `L > 0` and `T₀` such that the following holds for every
zero copy `q₀` with spectral point `ζ₀ = γ₀ + iδ` and every `η ≥ 0`. If `η + h + r + s₀ ≤ δ`,
`γ₀ ≥ T₀`, at most `M` copies sit at `ζ₀` or `ζ̄₀`, and every other copy at horizontal distance at
most `L` from `ζ₀` has `|Im| ≤ η`, then `cos(hD)Ξ` vanishes at a point within `r` of `ζ₀ − ih`
with imaginary part above `η`. -/
theorem exists_zero_cosShiftXi_of_isolated {h r s₀ : ℝ} (hh : 0 < h) (hr : 0 < r) (hs₀ : 0 < s₀)
    (M : ℕ) :
    ∃ L T₀ : ℝ, 0 < L ∧ ∀ (q₀ : XiZeroCopy) (η : ℝ), 0 ≤ η →
      η + h + r + s₀ ≤ (xiSpectralPoint q₀).im → T₀ ≤ (xiSpectralPoint q₀).re →
      (∀ G : Finset XiZeroCopy, (∀ q ∈ G, xiSpectralPoint q = xiSpectralPoint q₀ ∨
        xiSpectralPoint q = conj (xiSpectralPoint q₀)) → G.card ≤ M) →
      (∀ q, |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L →
        xiSpectralPoint q ≠ xiSpectralPoint q₀ → xiSpectralPoint q ≠ conj (xiSpectralPoint q₀) →
        |(xiSpectralPoint q).im| ≤ η) →
      ∃ z, ‖z - (xiSpectralPoint q₀ - h * I)‖ ≤ r ∧ η < z.im ∧ cosShiftXi h z = 0 := by
  obtain ⟨C, T₁, hC, hT₁, hwin⟩ := exists_window_lower_count
  exact ⟨isoL C h r s₀, isoT C T₁ h r s₀ M, isoL_pos hC hh hr hs₀,
    fun q₀ η hη hdepth hT hmult hiso =>
      exists_zero_cosShiftXi_of_isolated_explicit hC hT₁ hwin hh hr hs₀ M q₀ η hη hdepth hT hmult
        hiso⟩

end

end RHTower.CosineIsolatedDeepZero
