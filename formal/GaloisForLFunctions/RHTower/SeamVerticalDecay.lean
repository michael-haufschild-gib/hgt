/-
Vertical decay of ξ, and the complete aperiodicity that pins the functional equation as its unique
reflection.

`SeamRealAxisGrowth` discharges the aperiodicity hypothesis `hap` for *real* periods (via real-axis
growth), already forcing any reflection's fixed point onto the critical line.  The remaining case —
a *pure-imaginary* period, a reflection centered on the line but off `1/2` — needs decay in the
imaginary direction, supplied here by the reflection formula, no Stirling asymptotic required.

* `norm_Gamma_half_add_sq` / `gammaR_one_add_it_norm_sq` — `‖Γℝ(1 + it)‖² = 1/cosh(πt/2)`.  From
  `Γ(s)·Γ(1−s) = π/sin(πs)` at `s = ½ + i(t/2)`, where `1−s = s̄`, so `Γ(s)Γ(s̄) = |Γ(s)|²` and
  `sin(πs) = cosh(πt/2)`.
* `xi_vertical_decay` — `‖ξ(3 + it)‖ → 0` as `t → ∞`: the `Γℝ` factor's `e^{−πt/4}` decay dominates
  the polynomial `½·s(s−1)` and the bounded Dirichlet series `ζ(3 + it)`.
* `xi_not_periodic` — **ξ has no nonzero period.**  A period of nonzero real part gives, via reality,
  a real period (killed by growth); a pure-imaginary period is killed by the decay.
* `xi_entire_reflection_eq_fe` — **unconditional.**  Any reflection `s ↦ b − s` fixing ξ has `b = 1`:
  it is exactly the functional equation.  The `hap` hypothesis is now a theorem.
-/
import GaloisForLFunctions.RHTower.SeamRealAxisGrowth

open Complex Real Filter Topology

namespace RHTower

/-! ### §1 `‖Γℝ(1 + it)‖² = 1/cosh(πt/2)` via the reflection formula -/

/-- `‖Γ(½ + iy)‖²·cosh(πy) = π`, the reflection formula on the critical line: `1 − s = s̄` there, so
`Γ(s)Γ(1−s) = |Γ(s)|²` and `sin(πs) = cosh(πy)`. -/
theorem norm_Gamma_half_add_sq (y : ℝ) :
    ‖Complex.Gamma ((1:ℂ)/2 + y*I)‖^2 * Real.cosh (π*y) = π := by
  set s : ℂ := (1:ℂ)/2 + y*I with hs
  have hconj : 1 - s = (starRingEnd ℂ) s := by
    rw [hs]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
    ring
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at hrefl
  have hsin : Complex.sin (↑π * s) = ↑(Real.cosh (π*y)) := by
    have h1 : (↑π:ℂ) * s = ↑(π/2) + ↑(π*y)*I := by rw [hs]; push_cast; ring
    rw [h1, Complex.sin_add, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
       Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
    rw [Complex.cos_mul_I, ← Complex.ofReal_cosh]
  rw [hsin, ← Complex.ofReal_div] at hrefl
  have hval := Complex.ofReal_inj.mp hrefl
  rw [Complex.normSq_eq_norm_sq] at hval
  have hcosh_pos : 0 < Real.cosh (π*y) := Real.cosh_pos (π*y)
  rw [hval]; field_simp

/-- `‖Γℝ(1 + it)‖² = 1/cosh(πt/2)`. -/
theorem gammaR_one_add_it_norm_sq (t : ℝ) :
    ‖Gammaℝ ((1:ℂ) + t*I)‖^2 = 1 / Real.cosh (π*t/2) := by
  have hπ : 0 < π := Real.pi_pos
  have hcosh_pos : 0 < Real.cosh (π*t/2) := Real.cosh_pos _
  rw [Gammaℝ_def, norm_mul, mul_pow]
  have hbase : (1 + t*I) / 2 = (1:ℂ)/2 + ((t/2:ℝ):ℂ)*I := by push_cast; ring
  rw [hbase]
  have hnpi : ‖(↑π:ℂ) ^ (-(1 + t*I) / 2)‖ = π ^ (-(1:ℝ)/2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hπ]
    congr 1
    have hre_w : (-(1 + t*I) / 2).re = -(1:ℝ)/2 := by
      rw [show -(1 + t*I) / 2 = ((-(1:ℝ)/2 : ℝ):ℂ) + ((-(t/2):ℝ):ℂ)*I from by push_cast; ring,
        Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
      ring
    rw [hre_w]
  rw [hnpi]
  have hg := norm_Gamma_half_add_sq (t/2)
  have hcosh_eq : Real.cosh (π * (t/2)) = Real.cosh (π*t/2) := by congr 1; ring
  rw [hcosh_eq] at hg
  have hΓsq : ‖Complex.Gamma ((1:ℂ)/2 + ((t/2:ℝ):ℂ)*I)‖^2 = π / Real.cosh (π*t/2) := by
    rw [eq_div_iff hcosh_pos.ne']; linarith [hg]
  rw [hΓsq]
  have hpisq : (π ^ (-(1:ℝ)/2))^2 = π⁻¹ := by
    rw [← Real.rpow_natCast (π ^ (-(1:ℝ)/2)) 2, ← Real.rpow_mul hπ.le,
      show (-(1:ℝ)/2) * ((2:ℕ):ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
  rw [hpisq]
  field_simp

/-! ### §2 Vertical decay of ξ -/

/-- `‖Γℝ(1 + it)‖ ≤ √2 · exp(−πt/4)`: from `cosh x ≥ exp x / 2`. -/
theorem norm_gammaR_one_add_it_le (t : ℝ) :
    ‖Gammaℝ ((1:ℂ) + t*I)‖ ≤ Real.sqrt 2 * Real.exp (-(π*t/4)) := by
  have hcosh_pos : 0 < Real.cosh (π*t/2) := Real.cosh_pos _
  have hnn : 0 ≤ ‖Gammaℝ ((1:ℂ) + t*I)‖ := norm_nonneg _
  have hrhs_nn : 0 ≤ Real.sqrt 2 * Real.exp (-(π*t/4)) := by positivity
  have hsq2 : ‖Gammaℝ ((1:ℂ) + t*I)‖^2 ≤ 2 * Real.exp (-(π*t/2)) := by
    rw [gammaR_one_add_it_norm_sq, div_le_iff₀ hcosh_pos, Real.cosh_eq]
    have he : Real.exp (-(π*t/2)) * Real.exp (π*t/2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [he, sq_nonneg (Real.exp (-(π*t/2))), Real.exp_pos (π*t/2)]
  have hrhs_sq : (Real.sqrt 2 * Real.exp (-(π*t/4)))^2 = 2 * Real.exp (-(π*t/2)) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), ← Real.exp_nat_mul,
      show ((2:ℕ):ℝ)*-(π*t/4) = -(π*t/2) by push_cast; ring]
  calc ‖Gammaℝ ((1:ℂ) + t*I)‖ = Real.sqrt (‖Gammaℝ ((1:ℂ) + t*I)‖^2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (2 * Real.exp (-(π*t/2))) := Real.sqrt_le_sqrt hsq2
    _ = Real.sqrt 2 * Real.exp (-(π*t/4)) := by rw [← hrhs_sq, Real.sqrt_sq hrhs_nn]

/-- The Dirichlet series is bounded on `Re = 3`: `‖ζ(3 + it)‖ ≤ ∑ 1/n³`. -/
theorem norm_zeta_three_add_it_le (t : ℝ) :
    ‖riemannZeta ((3:ℂ) + t*I)‖ ≤ ∑' n : ℕ, (1:ℝ)/(n:ℝ)^3 := by
  have hre : (1:ℝ) < ((3:ℂ) + t*I).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.re_ofNat]; norm_num
  have hs0 : ((3:ℂ) + t*I) ≠ 0 := by
    intro h; rw [h] at hre; simp only [Complex.zero_re] at hre; linarith
  have hz : riemannZeta ((3:ℂ) + t*I) = ∑' n : ℕ, 1 / (n:ℂ)^((3:ℂ) + t*I) :=
    zeta_eq_tsum_one_div_nat_cpow hre
  have hterm : ∀ n : ℕ, ‖(1:ℂ) / (n:ℂ)^((3:ℂ) + t*I)‖ = (1:ℝ)/(n:ℝ)^3 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Complex.zero_cpow hs0]
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.re_ofNat]; norm_num
  have hsummable : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^3) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  have hsummable_norm : Summable (fun n : ℕ => ‖(1:ℂ) / (n:ℂ)^((3:ℂ) + t*I)‖) := by
    simpa only [hterm] using hsummable
  rw [hz]
  calc ‖∑' n : ℕ, (1:ℂ) / (n:ℂ)^((3:ℂ) + t*I)‖
      ≤ ∑' n : ℕ, ‖(1:ℂ) / (n:ℂ)^((3:ℂ) + t*I)‖ := norm_tsum_le_tsum_norm hsummable_norm
    _ = ∑' n : ℕ, (1:ℝ)/(n:ℝ)^3 := by simp_rw [hterm]

/-- A cubic times `e^{−πt/4}` tends to `0`. -/
theorem cubic_mul_exp_neg_tendsto :
    Tendsto (fun t : ℝ => (3 + t)^3 * Real.exp (-(π*t/4))) atTop (𝓝 0) := by
  have hπ : 0 < π := Real.pi_pos
  have hbase : Tendsto (fun v : ℝ => v^3 * Real.exp (-v)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
  have hv : Tendsto (fun t : ℝ => π*(3 + t)/4) atTop atTop := by
    apply Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 4)
    apply Filter.Tendsto.const_mul_atTop hπ
    exact tendsto_atTop_add_const_left _ 3 tendsto_id
  have hcomp := hbase.comp hv
  have hconst : Tendsto (fun t : ℝ => (4/π)^3 * ((π*(3+t)/4)^3 * Real.exp (-(π*(3+t)/4))))
      atTop (𝓝 ((4/π)^3 * 0)) := hcomp.const_mul _
  rw [mul_zero] at hconst
  have hEq : (fun t : ℝ => (4/π)^3 * ((π*(3+t)/4)^3 * Real.exp (-(π*(3+t)/4))))
      = (fun t : ℝ => ((3 + t)^3 * Real.exp (-(π*t/4))) * Real.exp (-(π*3/4))) := by
    funext t
    rw [show -(π*(3+t)/4) = -(π*t/4) + -(π*3/4) by ring, Real.exp_add]
    have hπ' : π ≠ 0 := hπ.ne'
    field_simp
  rw [hEq] at hconst
  have hfin := hconst.mul_const (Real.exp (π*3/4))
  simp only [zero_mul] at hfin
  refine hfin.congr (fun t => ?_)
  rw [mul_assoc, ← Real.exp_add, show -(π*3/4) + π*3/4 = 0 by ring, Real.exp_zero, mul_one]

/-- **ξ decays on the vertical line `Re = 3`.**  `‖ξ(3 + it)‖ → 0` as `t → ∞`, the `Γℝ` factor's
`e^{−πt/4}` decay dominating the polynomial `½·s(s−1)` and the bounded `ζ(3 + it)`. -/
theorem xi_vertical_decay :
    Tendsto (fun t : ℝ => ‖xi ((3:ℂ) + t*I)‖) atTop (𝓝 0) := by
  have hπ : 0 < π := Real.pi_pos
  set C : ℝ := ∑' n : ℕ, (1:ℝ)/(n:ℝ)^3 with hC
  have hCnn : 0 ≤ C := tsum_nonneg (fun n => by positivity)
  set D : ℝ := C * Real.sqrt 2 / (4*π) with hD
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖xi ((3:ℂ) + t*I)‖ ≤ D * ((3 + t)^3 * Real.exp (-(π*t/4))) := by
    intro t ht
    have hrezero : ∀ a : ℝ, ((a:ℂ) + t*I).re = a := by
      intro a
      rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]; ring
    have h0 : ((3:ℂ) + t*I) ≠ 0 := by
      intro h
      have hh : ((3:ℂ) + t*I).re = 0 := by rw [h, Complex.zero_re]
      rw [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at hh; norm_num at hh
    have h1 : ((3:ℂ) + t*I) ≠ 1 := by
      intro h
      have hh : ((3:ℂ) + t*I).re = 1 := by rw [h, Complex.one_re]
      rw [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at hh; norm_num at hh
    have hre3 : (0:ℝ) < ((3:ℂ) + t*I).re := by
      rw [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]; norm_num
    have hLam : completedRiemannZeta ((3:ℂ) + t*I)
        = riemannZeta ((3:ℂ) + t*I) * Gammaℝ ((3:ℂ) + t*I) := by
      rw [riemannZeta_def_of_ne_zero h0]; field_simp [Gammaℝ_ne_zero_of_re_pos hre3]
    have h1it : ((1:ℂ) + t*I) ≠ 0 := by
      intro h
      have hh : ((1:ℂ) + t*I).re = 0 := by rw [h, Complex.zero_re]
      rw [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at hh; norm_num at hh
    have hrec : Gammaℝ ((3:ℂ) + t*I) = Gammaℝ ((1:ℂ) + t*I) * ((1:ℂ) + t*I) / 2 / ↑π := by
      have hh := Gammaℝ_add_two h1it
      rwa [show ((1:ℂ) + t*I) + 2 = (3:ℂ) + t*I by ring] at hh
    have hxi : xi ((3:ℂ) + t*I)
        = ((3:ℂ) + t*I) * (((2:ℂ) + t*I)) / 2
          * (riemannZeta ((3:ℂ) + t*I) * (Gammaℝ ((1:ℂ) + t*I) * ((1:ℂ) + t*I) / 2 / ↑π)) := by
      rw [xi_eq_half_mul_completed h0 h1, hLam, hrec, show (((3:ℂ) + t*I) - 1) = (2:ℂ) + t*I by ring]
    have hnb : ∀ (a : ℝ), 0 ≤ a → ‖(a:ℂ) + t*I‖ ≤ a + t := by
      intro a ha
      have him : ((a:ℂ) + t*I).im = t := by
        rw [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re,
          Complex.I_im]; ring
      calc ‖(a:ℂ) + t*I‖ ≤ |((a:ℂ)+t*I).re| + |((a:ℂ)+t*I).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = a + t := by rw [hrezero a, him, abs_of_nonneg ha, abs_of_nonneg ht]
    have b3 : ‖(3:ℂ) + t*I‖ ≤ 3 + t := by
      have := hnb 3 (by norm_num); rwa [show ((3:ℝ):ℂ) = (3:ℂ) by norm_num] at this
    have b2 : ‖(2:ℂ) + t*I‖ ≤ 2 + t := by
      have := hnb 2 (by norm_num); rwa [show ((2:ℝ):ℂ) = (2:ℂ) by norm_num] at this
    have b1 : ‖(1:ℂ) + t*I‖ ≤ 1 + t := by
      have := hnb 1 (by norm_num); rwa [show ((1:ℝ):ℂ) = (1:ℂ) by norm_num] at this
    have hgR : ‖Gammaℝ ((1:ℂ) + t*I)‖ ≤ Real.sqrt 2 * Real.exp (-(π*t/4)) :=
      norm_gammaR_one_add_it_le t
    have hζ : ‖riemannZeta ((3:ℂ) + t*I)‖ ≤ C := norm_zeta_three_add_it_le t
    have hπc : ‖(↑π:ℂ)‖ = π := by rw [Complex.norm_real]; exact Real.norm_of_nonneg hπ.le
    have h2c : ‖(2:ℂ)‖ = 2 := by norm_num
    have hstep2 : (3 + t) * (2 + t) / 2 * (C * (Real.sqrt 2 * Real.exp (-(π*t/4)) * (1 + t) / 2 / π))
        ≤ D * ((3 + t)^3 * Real.exp (-(π*t/4))) := by
      rw [hD, show (3 + t) * (2 + t) / 2 * (C * (Real.sqrt 2 * Real.exp (-(π*t/4)) * (1 + t) / 2 / π))
        = C * Real.sqrt 2 / (4*π) * (((3+t)*(2+t)*(1+t)) * Real.exp (-(π*t/4))) by
        field_simp; ring]
      have hle : (3+t)*(2+t)*(1+t) ≤ (3+t)^3 := by nlinarith
      have hKnn : 0 ≤ C * Real.sqrt 2 / (4*π) := by positivity
      gcongr
    calc ‖xi ((3:ℂ) + t*I)‖
        = ‖(3:ℂ)+t*I‖ * ‖(2:ℂ)+t*I‖ / 2
          * (‖riemannZeta ((3:ℂ)+t*I)‖
            * (‖Gammaℝ ((1:ℂ)+t*I)‖ * ‖(1:ℂ)+t*I‖ / 2 / π)) := by
          rw [hxi]; simp only [norm_mul, norm_div, hπc, h2c]
      _ ≤ (3 + t) * (2 + t) / 2 * (C * (Real.sqrt 2 * Real.exp (-(π*t/4)) * (1 + t) / 2 / π)) := by
          gcongr
      _ ≤ D * ((3 + t)^3 * Real.exp (-(π*t/4))) := hstep2
  have hsq : Tendsto (fun t : ℝ => D * ((3 + t)^3 * Real.exp (-(π*t/4)))) atTop (𝓝 (D * 0)) :=
    cubic_mul_exp_neg_tendsto.const_mul D
  rw [mul_zero] at hsq
  refine squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) ?_ hsq
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht using hbound t ht

/-! ### §3 Complete aperiodicity and the unique reflection -/

/-- ξ is nonzero at `s = 3`. -/
theorem xi_three_ne_zero : xi (3:ℂ) ≠ 0 := by
  have h0 : (3:ℂ) ≠ 0 := by norm_num
  have h1 : (3:ℂ) ≠ 1 := by norm_num
  have hre : (0:ℝ) < (3:ℂ).re := by norm_num
  have hg : Gammaℝ (3:ℂ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hz : riemannZeta (3:ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hLam : completedRiemannZeta (3:ℂ) = riemannZeta 3 * Gammaℝ 3 := by
    rw [riemannZeta_def_of_ne_zero h0]; field_simp
  rw [xi_eq_half_mul_completed h0 h1, hLam]
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero h0 (by norm_num : ((3:ℂ) - 1) ≠ 0)) (by norm_num))
    (mul_ne_zero hz hg)

/-- ξ has no positive-imaginary period. -/
theorem xi_no_imaginary_period_pos {β : ℝ} (hβ : 0 < β)
    (hp : ∀ s, xi (s + (β:ℂ)*I) = xi s) : False := by
  have hper : Function.Periodic xi ((β:ℂ)*I) := hp
  have htn : Tendsto (fun n : ℕ => (n:ℝ)*β) atTop atTop :=
    Tendsto.atTop_mul_const hβ tendsto_natCast_atTop_atTop
  have hcomp := xi_vertical_decay.comp htn
  have hval' : ((fun t : ℝ => ‖xi ((3:ℂ) + t*I)‖) ∘ (fun n : ℕ => (n:ℝ)*β))
      = (fun _ : ℕ => ‖xi 3‖) := by
    funext n
    simp only [Function.comp_apply]
    have h := (hper.nat_mul n) 3
    have harg : (3:ℂ) + (((n:ℝ)*β : ℝ):ℂ)*I = 3 + (n:ℂ)*((β:ℂ)*I) := by push_cast; ring
    rw [harg, h]
  rw [hval'] at hcomp
  exact xi_three_ne_zero (norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hcomp))

/-- ξ has no nonzero pure-imaginary period. -/
theorem xi_no_imaginary_period {β : ℝ} (hβ : β ≠ 0)
    (hp : ∀ s, xi (s + (β:ℂ)*I) = xi s) : False := by
  rcases lt_or_gt_of_ne hβ with h | h
  · apply xi_no_imaginary_period_pos (β := -β) (by linarith)
    intro s
    have hn := xi_period_neg (ω := (β:ℂ)*I) hp s
    rwa [show ((-β:ℝ):ℂ)*I = -((β:ℂ)*I) by push_cast; ring]
  · exact xi_no_imaginary_period_pos h hp

/-- **ξ has no nonzero period.**  Real-part-nonzero periods are killed by real-axis growth (through
the induced real period), pure-imaginary ones by vertical decay. -/
theorem xi_not_periodic {ω : ℂ} (hω : ω ≠ 0) : ¬ (∀ s, xi (s + ω) = xi s) := by
  intro hp
  by_cases hre : ω.re = 0
  · have hωeq : ω = (ω.im:ℂ)*I := by apply Complex.ext <;> simp [hre]
    refine xi_no_imaginary_period (β := ω.im) ?_ ?_
    · intro h; apply hω; rw [hωeq, h]; simp
    · rw [← hωeq]; exact hp
  · have hperc := xi_period_conj hp
    have hsum := xi_period_add hp hperc
    rw [Complex.add_conj] at hsum
    set τ : ℝ := 2 * ω.re with hτ
    have hτ0 : τ ≠ 0 := fun h => hre (by rw [hτ] at h; linarith)
    rcases lt_or_gt_of_ne hτ0 with h | h
    · refine xi_not_real_periodic_pos (τ := -τ) (by linarith) (fun s => ?_)
      have hn := xi_period_neg hsum s
      rwa [show ((-τ:ℝ):ℂ) = -((τ:ℝ):ℂ) by push_cast; ring]
    · exact xi_not_real_periodic_pos h hsum

/-- **The functional equation is the unique reflection of ξ, unconditionally.**  Any reflection
`s ↦ b − s` fixing ξ has `b = 1`: it is exactly `s ↦ 1 − s`, fixed at `1/2`.  The former hypothesis
`hap` is now the theorem `xi_not_periodic`. -/
theorem xi_entire_reflection_eq_fe {b : ℂ} (hb : ∀ s, xi (b - s) = xi s) : b = 1 :=
  xi_entire_reflection_center_eq_half (fun _ hω => xi_not_periodic hω) hb

end RHTower
