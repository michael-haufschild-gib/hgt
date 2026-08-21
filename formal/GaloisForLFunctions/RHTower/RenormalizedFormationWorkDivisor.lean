import GaloisForLFunctions.RHTower.HighExponentShellSourcePole

/-!
# The renormalized survival transfer and its strict-right divisor

For a high-exponent shell pair `(m, r)` the inherited formation survival on the convergence ray is
`S_m(rs)/S_{rm}(s)`.  Removing the universal normalization pole gives the meromorphic survival
transfer `R_{m,r}(s) = S_m(rs)/((s-1)S_{rm}(s))`.  On the strict right half-plane the numerator is
holomorphic and zero-free, the denominator is the analytic shell residue unit, and therefore the
transfer is zero-free with poles exactly at the strict-right zeta zeros, of exactly their
multiplicity.  At the normalization point it is holomorphic and nonzero.
-/

open Complex

namespace RHTower

noncomputable section

/-- The meromorphic survival transfer `R_{m,r}(s) = S_m(rs)/((s-1)S_{rm}(s))`. -/
def survivalTransfer (m r : ℕ) (s : ℂ) : ℂ :=
  shellSource m ((r : ℂ) * s) / shellResidueUnit (r * m) s

theorem one_lt_re_natCast_mul {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : 1 / 2 < s.re) :
    1 < ((r : ℂ) * s).re := by
  have h : ((r : ℂ) * s).re = (r : ℝ) * s.re := by simp [Complex.mul_re]
  rw [h]
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith

/-- **The numerator is zero-free.**  On the strict right half-plane the dilated shell source has
no zeros: the dilated argument lies in the absolute convergence half-plane. -/
theorem shellSource_natCast_mul_ne_zero {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) {s : ℂ}
    (hs : 1 / 2 < s.re) : shellSource m ((r : ℂ) * s) ≠ 0 := by
  have h1 := one_lt_re_natCast_mul hr hs
  rw [shellSource]
  exact mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re h1)
    (shellMultiplier_ne_zero hm (by linarith))

theorem analyticAt_shellSource_natCast_mul {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) {s : ℂ}
    (hs : 1 / 2 < s.re) : AnalyticAt ℂ (fun z => shellSource m ((r : ℂ) * z)) s := by
  have h1 := one_lt_re_natCast_mul hr hs
  have hlin : AnalyticAt ℂ (fun z : ℂ => (r : ℂ) * z) s := analyticAt_const.mul analyticAt_id
  have hne1 : ((r : ℂ) * s) ≠ 1 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have hζ : AnalyticAt ℂ (fun z : ℂ => riemannZeta ((r : ℂ) * z)) s :=
    (analyticOn_riemannZeta _ hne1).comp hlin
  have hH : AnalyticAt ℂ (fun z : ℂ => shellMultiplier m ((r : ℂ) * z)) s :=
    (analyticAt_shellMultiplier hm (by linarith)).comp hlin
  exact hζ.mul hH

/-- **The denominator carries exactly the zeta divisor.** -/
theorem analyticOrderAt_shellResidueUnit {k : ℕ} (hk : 12 ≤ k) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) :
    analyticOrderAt (shellResidueUnit k) s = analyticOrderAt riemannZeta s := by
  have hzru : analyticOrderAt zetaResidueUnit s = analyticOrderAt riemannZeta s := by
    rw [analyticOrderAt_congr (zetaResidueUnit_eventuallyEq hs1)]
    have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta _ hs1
    have hmul : analyticOrderAt (fun z : ℂ => (z - 1) * riemannZeta z) s
        = analyticOrderAt (fun z : ℂ => z - 1) s + analyticOrderAt riemannZeta s :=
      analyticOrderAt_mul hlin hζ
    have hzero : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
      hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.2 hs1)
    rw [hmul, hzero, zero_add]
  have hH : AnalyticAt ℂ (shellMultiplier k) s := analyticAt_shellMultiplier hk hs
  have hmul : analyticOrderAt (shellResidueUnit k) s
      = analyticOrderAt zetaResidueUnit s + analyticOrderAt (shellMultiplier k) s :=
    analyticOrderAt_mul (analyticAt_zetaResidueUnit s) hH
  have hzero : analyticOrderAt (shellMultiplier k) s = 0 :=
    hH.analyticOrderAt_eq_zero.mpr (shellMultiplier_ne_zero hk hs)
  rw [hmul, hzero, add_zero, hzru]

/-- **Exact strict-right divisor.**  Away from the normalization point the survival transfer has
meromorphic order exactly the negative of the zeta vanishing order: it is zero-free, and its poles
are the strict-right zeta zeros with their multiplicities. -/
theorem meromorphicOrderAt_survivalTransfer {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    meromorphicOrderAt (survivalTransfer m r) s
      = -(ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt riemannZeta s)) := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  have hnum : AnalyticAt ℂ (fun z => shellSource m ((r : ℂ) * z)) s :=
    analyticAt_shellSource_natCast_mul hm hr hs
  have hden : AnalyticAt ℂ (shellResidueUnit (r * m)) s := analyticAt_shellResidueUnit hkm hs
  have hdiv : meromorphicOrderAt (survivalTransfer m r) s
      = meromorphicOrderAt (fun z => shellSource m ((r : ℂ) * z)) s
        - meromorphicOrderAt (shellResidueUnit (r * m)) s :=
    meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt
  have hnum0 : meromorphicOrderAt (fun z => shellSource m ((r : ℂ) * z)) s = 0 := by
    rw [hnum.meromorphicOrderAt_eq,
      hnum.analyticOrderAt_eq_zero.mpr (shellSource_natCast_mul_ne_zero hm hr hs)]
    rfl
  rw [hdiv, hnum0, hden.meromorphicOrderAt_eq, analyticOrderAt_shellResidueUnit hkm hs hs1,
    zero_sub]

/-- The survival transfer is zero-free wherever it is defined. -/
theorem survivalTransfer_ne_zero {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) {s : ℂ}
    (hs : 1 / 2 < s.re) (hden : shellResidueUnit (r * m) s ≠ 0) :
    survivalTransfer m r s ≠ 0 :=
  div_ne_zero (shellSource_natCast_mul_ne_zero hm hr hs) hden

/-! ## The normalization point -/

@[simp] theorem survivalTransfer_one (m r : ℕ) :
    survivalTransfer m r 1 = shellSource m (r : ℂ) / shellMultiplier (r * m) 1 := by
  rw [survivalTransfer, shellResidueUnit_one, mul_one]

theorem analyticAt_survivalTransfer_one {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    AnalyticAt ℂ (survivalTransfer m r) 1 := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  have hhalf : (1 : ℝ) / 2 < (1 : ℂ).re := by norm_num
  exact (analyticAt_shellSource_natCast_mul hm hr hhalf).div
    (analyticAt_shellResidueUnit hkm hhalf)
    (shellResidueUnit_one_ne_zero (by omega))

theorem survivalTransfer_one_ne_zero {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    survivalTransfer m r 1 ≠ 0 := by
  have hhalf : (1 : ℝ) / 2 < (1 : ℂ).re := by norm_num
  exact survivalTransfer_ne_zero hm hr hhalf
    (shellResidueUnit_one_ne_zero (le_trans (by omega) (Nat.le_mul_of_pos_left m (by omega))))

/-! ## Renormalization -/

/-- **Exact renormalization.**  Multiplying the transfer by the normalization factor recovers the
inherited formation survival. -/
theorem survivalTransfer_mul_sub_one {m r : ℕ} {s : ℂ} (hs1 : s ≠ 1)
    (hden : shellMultiplier (r * m) s ≠ 0) (hζ : riemannZeta s ≠ 0) :
    survivalTransfer m r s * (s - 1) = shellSource m ((r : ℂ) * s) / shellSource (r * m) s := by
  have hzru : zetaResidueUnit s = (s - 1) * riemannZeta s := by
    rw [zetaResidueUnit, Function.update_of_ne hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  rw [survivalTransfer, shellResidueUnit, hzru]
  simp only [shellSource]
  field_simp

/-! ## Positivity on the convergence ray -/

theorem tsum_inv_pow_pos {k : ℕ} (hk : 1 < k) : 0 < ∑' n : ℕ, ((n : ℝ) ^ k)⁻¹ := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ k)⁻¹) := by
    simpa using Real.summable_one_div_nat_pow.mpr hk
  have h1 : (((1 : ℕ) : ℝ) ^ k)⁻¹ ≤ ∑' n : ℕ, ((n : ℝ) ^ k)⁻¹ :=
    hsum.le_tsum 1 (fun i _ => by positivity)
  simp at h1
  linarith

theorem riemannZeta_natCast_eq_ofReal_tsum {k : ℕ} (hk : 1 < k) :
    riemannZeta ((k : ℕ) : ℂ) = ((∑' n : ℕ, ((n : ℝ) ^ k)⁻¹ : ℝ) : ℂ) := by
  have hre : 1 < (((k : ℕ) : ℂ)).re := by
    simpa using (by exact_mod_cast hk : (1 : ℝ) < (k : ℝ))
  rw [zeta_eq_tsum_one_div_nat_cpow hre, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.cpow_natCast]
  push_cast
  ring

theorem tsum_inv_pow_strict_lt {a b : ℕ} (ha : 1 < a) (hab : a < b) :
    ∑' n : ℕ, ((n : ℝ) ^ b)⁻¹ < ∑' n : ℕ, ((n : ℝ) ^ a)⁻¹ := by
  have hsa : Summable (fun n : ℕ => ((n : ℝ) ^ a)⁻¹) := by
    simpa using Real.summable_one_div_nat_pow.mpr ha
  have hsb : Summable (fun n : ℕ => ((n : ℝ) ^ b)⁻¹) := by
    simpa using Real.summable_one_div_nat_pow.mpr (by omega : 1 < b)
  refine Summable.tsum_lt_tsum (i := 2) (fun n => ?_) ?_ hsb hsa
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, zero_pow (by omega : b ≠ 0), zero_pow (by omega : a ≠ 0)]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpow : ((n : ℝ)) ^ a ≤ ((n : ℝ)) ^ b := pow_le_pow_right₀ hn1 (le_of_lt hab)
      exact inv_anti₀ (by positivity) hpow
  · have hc : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hc]
    have h2 : (2 : ℝ) ^ a < (2 : ℝ) ^ b := pow_lt_pow_right₀ (by norm_num) hab
    exact inv_strictAnti₀ (by positivity) h2

theorem exists_pos_shellMultiplier_natCast {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) :
    ∃ x : ℝ, 0 < x ∧ shellMultiplier m ((k : ℕ) : ℂ) = (x : ℂ) := by
  have hmk : 1 < m * k := by nlinarith
  have hmk1 : m * k < (m + 1) * k := by nlinarith
  set A : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (m * k))⁻¹ with hAdef
  set B : ℝ := ∑' n : ℕ, ((n : ℝ) ^ ((m + 1) * k))⁻¹ with hBdef
  have hA0 : 0 < A := tsum_inv_pow_pos hmk
  have hB0 : 0 < B := tsum_inv_pow_pos (by omega)
  have hBA : B < A := tsum_inv_pow_strict_lt hmk hmk1
  refine ⟨B⁻¹ - A⁻¹, by
    have : A⁻¹ < B⁻¹ := inv_strictAnti₀ hB0 hBA
    linarith, ?_⟩
  have hcast1 : (((m : ℂ)) + 1) * ((k : ℕ) : ℂ) = (((m + 1) * k : ℕ) : ℂ) := by push_cast; ring
  have hcast2 : ((m : ℂ)) * ((k : ℕ) : ℂ) = ((m * k : ℕ) : ℂ) := by push_cast; ring
  rw [shellMultiplier, hcast1, hcast2, riemannZeta_natCast_eq_ofReal_tsum (by omega),
    riemannZeta_natCast_eq_ofReal_tsum hmk, ← hAdef, ← hBdef]
  push_cast
  ring

/-- **The transfer is a positive real at the normalization point**, so the renormalized formation
work there is the real logarithm `log(H_{rm}(1)/S_m(r))` (DWP.9). -/
theorem survivalTransfer_one_eq_ofReal_pos {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    ∃ S H : ℝ, 0 < S ∧ 0 < H ∧ shellSource m ((r : ℕ) : ℂ) = (S : ℂ) ∧
      shellMultiplier (r * m) 1 = (H : ℂ) ∧
      survivalTransfer m r 1 = ((S / H : ℝ) : ℂ) ∧
      -Real.log (S / H) = Real.log (H / S) := by
  have hZ := riemannZeta_natCast_eq_ofReal_tsum (k := r) (by omega)
  have hZ0 : 0 < ∑' n : ℕ, ((n : ℝ) ^ r)⁻¹ := tsum_inv_pow_pos (by omega)
  obtain ⟨Hm, hHm0, hHm⟩ := exists_pos_shellMultiplier_natCast (m := m) (k := r) (by omega)
    (by omega)
  obtain ⟨H, hH0, hH⟩ := shellMultiplier_one_eq_ofReal_pos (m := r * m)
    (le_trans (by omega) (Nat.le_mul_of_pos_left m (by omega)))
  refine ⟨(∑' n : ℕ, ((n : ℝ) ^ r)⁻¹) * Hm, H, by positivity, hH0, ?_, hH, ?_, ?_⟩
  · rw [shellSource, hZ, hHm, Complex.ofReal_mul]
  · rw [survivalTransfer_one, shellSource, hZ, hHm, hH, ← Complex.ofReal_mul,
      ← Complex.ofReal_div]
  · rw [← Real.log_inv, inv_div]

end

end RHTower
