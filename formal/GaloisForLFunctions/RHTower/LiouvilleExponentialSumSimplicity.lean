import GaloisForLFunctions.RHTower.LiouvilleSummatoryPolyaBoundary

/-!
# The exponential Liouville sum: a one-sided `√t` bound forces RH and simple zeros

Let `J(t) = Σ_{n ≥ 1} λ(n) e^{-nt}/n`.  Its Mellin transform is

`∫_0^∞ J(t) t^{s-1} dt = Γ(s) Σ λ(n) n^{-s-1} = Γ(s) ζ(2s+2)/ζ(s+1) = Γ(s+1) Z(2s+2)/((2s+1) Z(s+1))`

for `Re s > 0` (`mellin_liouvilleExpSum`, `Gamma_mul_LSeries_eq_kernel`), with `Z(w) = (w-1)ζ(w)`.
The kernel is meromorphic on `Re s > -½` with poles exactly at `ρ - 1`, `ζ(ρ) = 0`, and a simple
pole at `s = -½` whose residue `-√π/ζ(½) ≈ 1.214` is positive: `J(t)` carries the positive bias
`≈ 1.214√t` as `t → 0`.

**Theorem** (`riemannHypothesis_of_liouvilleExpSum_lower`,
`deriv_zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower`).  If `J(t) ≥ -C√t` for `0 < t ≤ t₀`,
then the Riemann hypothesis holds and every zero of `ζ` on the critical line is simple.

In the variable `t = e^{-u}`, the density `J(e^{-u}) + C' e^{-u/2}` is nonnegative on `u > 0`.  Its
Laplace transform equals `Γ(z) L(λ, z+1) - E(z) + C'/(z+½)`, where `E(z) = ∫_{-∞}^0 e^{-zu}
J(e^{-u}) du` is entire (`liouvilleExpTail`).  The continuation is analytic at every real point of
`(-½, ∞)`, so Landau's theorem puts the abscissa at `-½`, and the identity theorem gives
`(∫ e^{-zu} dν + E(z) - C'/(z+½))(2z+1) Z(z+1) = Γ(z+1) Z(2z+2)` on `Re z > -½`.  A zero of `Z`
right of the line would make the right side vanish.  At a critical zero of order `m`, the left side
is `O(r^{m-1})` along `z = ρ - 1 + r`, because `r ∫ e^{(½-r)u} dν` stays bounded, while the right
side tends to `Γ(ρ)Z(2ρ) ≠ 0`, so `m = 1`.

If `K(t) = J(t) - tJ'(t) ≥ 0` on `(0, t₀]`, then `J(t)/t` decreases there, so `J(t) ≥ t J(t₀)/t₀
≥ -C√t`, and the theorem applies: positivity of the exponential Liouville current implies RH
together with simplicity of every critical zero.  Exact (`ε`-free) one-sided laws in the Liouville
lane are therefore at least as strong as RH plus simplicity; only `ε`-lossy versions are
RH-equivalent.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open scoped LSeries.notation

namespace RHTower

noncomputable section

/-! ## The exponential Liouville sum `J(t) = Σ λ(n) e^{-nt}/n` -/

/-- The coefficient `λ(n)/n`. -/
def liouvilleExpCoeff (n : ℕ) : ℝ := ((ArithmeticFunction.liouville n : ℤ) : ℝ) / n

/-- `J(t) = Σ λ(n) e^{-nt}/n`. -/
def liouvilleExpSum (t : ℝ) : ℝ := ∑' n : ℕ, liouvilleExpCoeff n * Real.exp (-(n * t))

theorem abs_liouvilleExpCoeff_le (n : ℕ) : |liouvilleExpCoeff n| ≤ 1 / n := by
  unfold liouvilleExpCoeff
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (abs_liouville_le_one n) (Nat.cast_nonneg n)

theorem abs_liouvilleExpTerm_le (n : ℕ) {t : ℝ} :
    |liouvilleExpCoeff n * Real.exp (-(n * t))| ≤ Real.exp (-t) ^ n / n := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul, show (n : ℝ) * -t = -(n * t) by
    ring, div_eq_mul_one_div, mul_comm (Real.exp _)]
  exact mul_le_mul_of_nonneg_right (abs_liouvilleExpCoeff_le n) (Real.exp_pos _).le

theorem hasSum_log_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => r ^ n / n) (-Real.log (1 - r)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := r) (by rw [abs_of_nonneg hr0]; exact hr1)
  have h' : HasSum (fun n : ℕ => r ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) (-Real.log (1 - r)) := by
    simpa using h
  exact (hasSum_nat_add_iff' 1).mp (by simpa using h')

theorem summable_liouvilleExpTerm {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => liouvilleExpCoeff n * Real.exp (-(n * t)) := by
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_norm_bounded (hasSum_log_bound (Real.exp_pos _).le hr1).summable ?_
  intro n; rw [Real.norm_eq_abs]; exact abs_liouvilleExpTerm_le n

/-- `|J(t)| ≤ -log(1 - e^{-t})`. -/
theorem abs_liouvilleExpSum_le {t : ℝ} (ht : 0 < t) :
    |liouvilleExpSum t| ≤ -Real.log (1 - Real.exp (-t)) := by
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := summable_liouvilleExpTerm ht
  have hb := hasSum_log_bound (Real.exp_pos (-t)).le hr1
  unfold liouvilleExpSum
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [← hb.tsum_eq]
  exact hs.norm.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact abs_liouvilleExpTerm_le n)
    hb.summable

/-- For `0 < t ≤ 1`: `|J(t)| ≤ 1 + log(1/t)`. -/
theorem abs_liouvilleExpSum_le_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |liouvilleExpSum t| ≤ 1 + Real.log (1 / t) := by
  refine (abs_liouvilleExpSum_le ht).trans ?_
  have he : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp t])
  have h1 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : 1 - 1 / (1 + t) = t / (1 + t) := by field_simp; ring
    linarith
  have hpos : 0 < t / (1 + t) := by positivity
  have h2 : -Real.log (1 - Real.exp (-t)) ≤ -Real.log (t / (1 + t)) := by
    linarith [Real.log_le_log hpos h1]
  have h3 : -Real.log (t / (1 + t)) = Real.log (1 + t) + Real.log (1 / t) := by
    rw [Real.log_div ht.ne' (by linarith), one_div, Real.log_inv]; ring
  have h4 : Real.log (1 + t) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    have := Real.add_one_le_exp 1; linarith
  linarith

/-- For `t ≥ 1`: `|J(t)| ≤ 2 e^{-t}`. -/
theorem abs_liouvilleExpSum_le_large {t : ℝ} (ht : 1 ≤ t) :
    |liouvilleExpSum t| ≤ 2 * Real.exp (-t) := by
  refine (abs_liouvilleExpSum_le (by linarith)).trans ?_
  set r := Real.exp (-t) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ≤ 1 / 2 := by
    rw [hr]
    calc Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.exp_one_gt_d9; norm_num; linarith
  have h1 : -Real.log (1 - r) ≤ r / (1 - r) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - r) by
      exact div_pos one_pos (by linarith))
    rw [one_div, Real.log_inv] at h
    have h1r : (1 - r) ≠ 0 := by linarith
    have : (1 - r)⁻¹ - 1 = r / (1 - r) := by field_simp; ring
    linarith
  have h2 : r / (1 - r) ≤ 2 * r := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

theorem continuousOn_liouvilleExpSum : ContinuousOn liouvilleExpSum (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : 0 < t₀ := ht₀
  have hcont : ContinuousOn liouvilleExpSum (Ioi (t₀ / 2)) := by
    have hr1 : Real.exp (-(t₀ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    refine continuousOn_tsum (u := fun n : ℕ => Real.exp (-(t₀ / 2)) ^ n / n)
      (f := fun (n : ℕ) (t : ℝ) => liouvilleExpCoeff n * Real.exp (-(n * t))) (fun n => ?_)
      (hasSum_log_bound (Real.exp_pos _).le hr1).summable ?_
    · exact (by fun_prop : Continuous fun t : ℝ => liouvilleExpCoeff n * Real.exp (-(n * t))).continuousOn
    · intro n t ht
      rw [Real.norm_eq_abs]
      refine (abs_liouvilleExpTerm_le n).trans ?_
      simp only [mem_Ioi] at ht
      gcongr
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-! ## The Mellin transform -/

/-- `∫_0^∞ J(t) t^{s-1} dt = Γ(s) L(λ, s+1)` for `Re s > 0`. -/
theorem mellin_liouvilleExpSum {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t => (liouvilleExpSum t : ℂ)) s = Gamma s * LSeries ↗liouvilleC (s + 1) := by
  set a : ℕ → ℂ := fun n => (liouvilleExpCoeff n : ℂ) with ha
  have hp : ∀ n : ℕ, a n = 0 ∨ 0 < (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [ha, liouvilleExpCoeff]
    · right; exact_mod_cast hn
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t))
      ((liouvilleExpSum t : ℝ) : ℂ) := by
    intro t ht
    have h := (summable_liouvilleExpTerm (t := t) ht).hasSum
    have h' := (Complex.ofRealCLM.hasSum h)
    simp only [Complex.ofRealCLM_apply] at h'
    unfold liouvilleExpSum
    convert h' using 1
    funext n
    simp [ha, neg_mul]
  have hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ s.re := by
    have hp1 : 1 < 1 + s.re := by linarith
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (Real.summable_one_div_nat_rpow.mpr hp1)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha, liouvilleExpCoeff]; exact Real.rpow_nonneg le_rfl _
    have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [ha, Complex.norm_real, Real.norm_eq_abs, Real.rpow_add hn1, Real.rpow_one]
    calc |liouvilleExpCoeff n| / (n : ℝ) ^ s.re ≤ (1 / n) / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right (abs_liouvilleExpCoeff_le n) (by positivity)
      _ = 1 / ((n : ℝ) * (n : ℝ) ^ s.re) := by field_simp
  have hM := hasSum_mellin hp hs hF hsum
  rw [← hM.tsum_eq, LSeries, ← tsum_mul_left]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha, liouvilleExpCoeff, LSeries.term_def]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [LSeries.term_def, if_neg hn.ne', Complex.cpow_add _ _ hn0, Complex.cpow_one]
  simp only [ha, liouvilleExpCoeff, liouvilleC_apply]
  push_cast
  ring

/-! ## The logarithmic variable `t = e^{-u}` -/

theorem rexp_neg_hasDerivWithinAt : ∀ x ∈ univ,
    HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

theorem rexp_neg_image_univ : Real.exp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

theorem rexp_neg_injOn_univ : univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- `∫_0^∞ t^{s-1} f(t) dt = ∫_ℝ e^{-su} f(e^{-u}) du`. -/
theorem mellin_eq_integral_cexp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, cexp (-s * u) * f (Real.exp (-u)) := by
  rw [mellin, ← rexp_neg_image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    rexp_neg_hasDerivWithinAt rexp_neg_injOn_univ, Measure.restrict_univ]
  congr 1
  funext u
  simp only [Function.comp_apply, abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul,
    smul_eq_mul]
  have hlog : Complex.log ((Real.exp (-u) : ℝ) : ℂ) = ((-u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos (-u)).ne'), hlog,
    Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- The density in the logarithmic variable, `F(u) = J(e^{-u})`. -/
def liouvilleExpLog (u : ℝ) : ℝ := liouvilleExpSum (Real.exp (-u))

theorem continuous_liouvilleExpLog : Continuous liouvilleExpLog :=
  continuousOn_liouvilleExpSum.comp_continuous (by fun_prop) fun u => Real.exp_pos (-u)

/-- `|F(u)| ≤ 2 k! e^{ku}` for `u ≤ 0`. -/
theorem abs_liouvilleExpLog_le_of_nonpos (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    |liouvilleExpLog u| ≤ 2 * k.factorial * Real.exp (k * u) := by
  unfold liouvilleExpLog
  have ht : 1 ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
  refine (abs_liouvilleExpSum_le_large ht).trans ?_
  have hx := Real.pow_div_factorial_le_exp (Real.exp (-u)) (Real.exp_pos _).le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hpow : Real.exp (-u) ^ k = Real.exp (-(k * u)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hpow] at hx
  have h1 : Real.exp (-Real.exp (-u)) ≤ k.factorial * Real.exp (k * u) := by
    rw [div_le_iff₀ hk] at hx
    have he : Real.exp (-(k * u)) * Real.exp (k * u) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-Real.exp (-u))
    have hpos2 := Real.exp_pos (k * u)
    calc Real.exp (-Real.exp (-u)) = Real.exp (-Real.exp (-u)) *
          (Real.exp (-(k * u)) * Real.exp (k * u)) := by rw [he, mul_one]
      _ = (Real.exp (-(k * u)) * Real.exp (-Real.exp (-u))) * Real.exp (k * u) := by ring
      _ ≤ (k.factorial) * Real.exp (k * u) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos2.le
          have := Real.exp_neg (Real.exp (-u))
          rw [this, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
          linarith
  linarith

/-- `|F(u)| ≤ 1 + u` for `u ≥ 0`. -/
theorem abs_liouvilleExpLog_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    |liouvilleExpLog u| ≤ 1 + u := by
  unfold liouvilleExpLog
  have h := abs_liouvilleExpSum_le_small (Real.exp_pos (-u)) (Real.exp_le_one_iff.mpr (by linarith))
  rwa [one_div, ← Real.exp_neg, neg_neg, Real.log_exp] at h

/-- The tail `E(s) = ∫_{-∞}^0 e^{-su} F(u) du`, entire in `s`. -/
def liouvilleExpTail (s : ℂ) : ℂ := ∫ u in Iic (0 : ℝ), cexp (-s * u) * (liouvilleExpLog u : ℂ)

theorem integrableOn_Iic_liouvilleExpIntegrand {s : ℂ} : IntegrableOn
    (fun u : ℝ => cexp (-s * u) * (liouvilleExpLog u : ℂ)) (Iic 0) := by
  set k : ℕ := ⌈|s.re|⌉₊ + 1 with hk
  have hkR : |s.re| + 1 ≤ k := by
    rw [hk]; push_cast; linarith [Nat.le_ceil |s.re|]
  have hmaj : IntegrableOn (fun u : ℝ => 2 * k.factorial * Real.exp ((k - |s.re|) * u)) (Iic 0) :=
    (integrableOn_exp_mul_Iic (by linarith) 0).const_mul _
  refine hmaj.mono' ((by fun_prop : Continuous fun u : ℝ => cexp (-s * u)).mul
    (Complex.continuous_ofReal.comp continuous_liouvilleExpLog)).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Iic] with u hu
  have hu0 : u ≤ 0 := hu
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_liouvilleExpLog_le_of_nonpos k hu0
  have h2 : (-s * (u : ℂ)).re = -s.re * u := by simp
  rw [h2]
  have h3 : Real.exp (-s.re * u) ≤ Real.exp (-|s.re| * u) := Real.exp_le_exp.mpr (by
    nlinarith [le_abs_self s.re, neg_abs_le s.re])
  calc Real.exp (-s.re * u) * |liouvilleExpLog u| ≤ Real.exp (-|s.re| * u) *
        (2 * k.factorial * Real.exp (k * u)) :=
        mul_le_mul h3 h1 (abs_nonneg _) (Real.exp_pos _).le
    _ = 2 * k.factorial * Real.exp ((k - |s.re|) * u) := by
        rw [mul_comm, mul_assoc, ← Real.exp_add]; ring_nf

theorem integrableOn_Ioi_liouvilleExpIntegrand {s : ℂ} (hs : 0 < s.re) : IntegrableOn
    (fun u : ℝ => cexp (-s * u) * (liouvilleExpLog u : ℂ)) (Ioi 0) := by
  have hmaj : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u) +
      (2 / s.re) * Real.exp (-(s.re / 2) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs).add ((exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _)
  refine hmaj.mono' ((by fun_prop : Continuous fun u : ℝ => cexp (-s * u)).mul
    (Complex.continuous_ofReal.comp continuous_liouvilleExpLog)).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_liouvilleExpLog_le_of_nonneg hu0.le
  have h2 : (-s * (u : ℂ)).re = -s.re * u := by simp
  rw [h2]
  have hu2 : u ≤ (2 / s.re) * Real.exp ((s.re / 2) * u) := by
    have h := Real.add_one_le_exp ((s.re / 2) * u)
    have h' : (s.re / 2) * u ≤ Real.exp ((s.re / 2) * u) := by linarith
    calc u = (2 / s.re) * ((s.re / 2) * u) := by field_simp
      _ ≤ (2 / s.re) * Real.exp ((s.re / 2) * u) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
  have hE := Real.exp_pos (-s.re * u)
  calc Real.exp (-s.re * u) * |liouvilleExpLog u| ≤ Real.exp (-s.re * u) * (1 + u) :=
        mul_le_mul_of_nonneg_left h1 hE.le
    _ ≤ Real.exp (-s.re * u) * (1 + (2 / s.re) * Real.exp ((s.re / 2) * u)) := by gcongr
    _ = Real.exp (-s.re * u) + (2 / s.re) * Real.exp (-(s.re / 2) * u) := by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm (Real.exp _) (2 / s.re), mul_assoc,
          ← Real.exp_add]; ring_nf

/-- **Split Mellin identity.**  For `Re s > 0`:
`∫_0^∞ e^{-su} F(u) du = Γ(s) L(λ, s+1) - E(s)`. -/
theorem integral_Ioi_liouvilleExpLog {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Ioi (0 : ℝ), cexp (-s * u) * (liouvilleExpLog u : ℂ)
      = Gamma s * LSeries ↗liouvilleC (s + 1) - liouvilleExpTail s := by
  have hM := mellin_liouvilleExpSum hs
  rw [mellin_eq_integral_cexp] at hM
  have hint : Integrable (fun u : ℝ => cexp (-s * u) * (liouvilleExpLog u : ℂ)) := by
    have := (integrableOn_Ioi_liouvilleExpIntegrand hs).union (integrableOn_Iic_liouvilleExpIntegrand (s := s))
    rwa [Ioi_union_Iic, integrableOn_univ] at this
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint
  rw [compl_Ioi] at hsplit
  unfold liouvilleExpTail
  rw [← hM]
  simp only [liouvilleExpLog] at hsplit ⊢
  linear_combination hsplit

/-! ## The tail is entire -/

theorem hasDerivAt_liouvilleExpTail (s₀ : ℂ) :
    HasDerivAt liouvilleExpTail
      (∫ u in Iic (0 : ℝ), -(u : ℂ) * cexp (-s₀ * u) * (liouvilleExpLog u : ℂ)) s₀ := by
  set R : ℝ := |s₀.re| + 1 with hR
  set k : ℕ := ⌈R⌉₊ + 2 with hk
  have hkR : R + 2 ≤ k := by rw [hk]; push_cast; linarith [Nat.le_ceil R]
  set bound : ℝ → ℝ := fun u => 2 * k.factorial * Real.exp ((k - R - 1) * u) with hbound
  have hbint : IntegrableOn bound (Iic 0) :=
    (integrableOn_exp_mul_Iic (by linarith) 0).const_mul _
  have hcont : ∀ s : ℂ, Continuous fun u : ℝ => cexp (-s * u) * (liouvilleExpLog u : ℂ) :=
    fun s => (by fun_prop : Continuous fun u : ℝ => cexp (-s * u)).mul
      (Complex.continuous_ofReal.comp continuous_liouvilleExpLog)
  have hcont' : Continuous fun u : ℝ => -(u : ℂ) * cexp (-s₀ * u) * (liouvilleExpLog u : ℂ) :=
    ((by fun_prop : Continuous fun u : ℝ => -(u : ℂ) * cexp (-s₀ * u))).mul
      (Complex.continuous_ofReal.comp continuous_liouvilleExpLog)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Iic (0 : ℝ)))
    (F := fun s u => cexp (-s * u) * (liouvilleExpLog u : ℂ))
    (F' := fun s u => -(u : ℂ) * cexp (-s * u) * (liouvilleExpLog u : ℂ))
    (bound := bound) (x₀ := s₀) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable) integrableOn_Iic_liouvilleExpIntegrand
    hcont'.aestronglyMeasurable ?_ hbint ?_
  · exact h.2
  · filter_upwards [self_mem_ae_restrict measurableSet_Iic] with u hu s hs
    have hu0 : u ≤ 0 := hu
    have hsre : |s.re| ≤ R := by
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : ‖s - s₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hs
      rw [hR]
      calc |s.re| = |(s.re - s₀.re) + s₀.re| := by ring_nf
        _ ≤ |s.re - s₀.re| + |s₀.re| := abs_add_le _ _
        _ ≤ |s₀.re| + 1 := by linarith
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs]
    have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
    rw [hre]
    have h1 := abs_liouvilleExpLog_le_of_nonpos k hu0
    have h2 : Real.exp (-s.re * u) ≤ Real.exp (-R * u) := Real.exp_le_exp.mpr (by
      nlinarith [le_abs_self s.re, neg_abs_le s.re])
    have h3 : |u| ≤ Real.exp (-u) := by
      rw [abs_of_nonpos hu0]; linarith [Real.add_one_le_exp (-u)]
    calc |u| * Real.exp (-s.re * u) * |liouvilleExpLog u|
        ≤ Real.exp (-u) * Real.exp (-R * u) * (2 * k.factorial * Real.exp (k * u)) := by
          gcongr
    _ = bound u := by
          simp only [hbound]
          rw [show ((k : ℝ) - R - 1) * u = -u + -R * u + k * u by ring, Real.exp_add,
            Real.exp_add]
          ring
  · filter_upwards with u s _
    have h1 : HasDerivAt (fun s : ℂ => -s * (u : ℂ)) (-(u : ℂ)) s := by
      simpa using (hasDerivAt_id s).neg.mul_const (u : ℂ)
    exact (h1.cexp.mul_const (liouvilleExpLog u : ℂ)).congr_deriv (by ring)

theorem differentiable_liouvilleExpTail : Differentiable ℂ liouvilleExpTail :=
  fun s => (hasDerivAt_liouvilleExpTail s).differentiableAt

/-! ## The continuation kernel -/

/-- `κ(z) = Γ(z+1) Z(2z+2)/((2z+1) Z(z+1)) = Γ(z) ζ(2z+2)/ζ(z+1)`. -/
def liouvilleExpKernel (z : ℂ) : ℂ :=
  Gamma (z + 1) * zetaResidueUnit (2 * z + 2) / ((2 * z + 1) * zetaResidueUnit (z + 1))

theorem analyticAt_Gamma_of_pos_re {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Gamma w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z fun m h => by
      have : (0 : ℝ) < z.re := hz
      rw [h] at this; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds hw)

theorem analyticAt_liouvilleExpKernel {z : ℂ} (hz : -1 < z.re) (h2 : 2 * z + 1 ≠ 0)
    (hZ : zetaResidueUnit (z + 1) ≠ 0) : AnalyticAt ℂ liouvilleExpKernel z := by
  unfold liouvilleExpKernel
  have hG : AnalyticAt ℂ (fun z : ℂ => Gamma (z + 1)) z :=
    (analyticAt_Gamma_of_pos_re (by simp; linarith)).comp (analyticAt_id.add analyticAt_const)
  exact (hG.mul ((analyticAt_zetaResidueUnit _).comp
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const))).div
    (((analyticAt_const.mul analyticAt_id).add analyticAt_const).mul
      ((analyticAt_zetaResidueUnit _).comp (analyticAt_id.add analyticAt_const)))
    (mul_ne_zero h2 hZ)

theorem zetaResidueUnit_ne_zero_of_one_lt_re {w : ℂ} (hw : 1 < w.re) : zetaResidueUnit w ≠ 0 := by
  have hw1 : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw; linarith
  rw [zetaResidueUnit, Function.update_of_ne hw1]
  exact mul_ne_zero (sub_ne_zero.mpr hw1) (riemannZeta_ne_zero_of_one_lt_re hw)

/-- On `Re z > 0`: `Γ(z) L(λ, z+1) = κ(z)`. -/
theorem Gamma_mul_LSeries_eq_kernel {z : ℂ} (hz : 0 < z.re) :
    Gamma z * LSeries ↗liouvilleC (z + 1) = liouvilleExpKernel z := by
  have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  have hre1 : 1 < (z + 1).re := by simp; linarith
  have hre2 : 1 < (2 * z + 2).re := by simp; linarith
  have h1 : z + 1 ≠ 1 := by intro h; apply hz0; linear_combination h
  have h2 : 2 * z + 2 ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h21 : 2 * z + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [LSeries_liouvilleC_eq_div hre1, liouvilleExpKernel, Complex.Gamma_add_one z hz0,
    zetaResidueUnit, Function.update_of_ne h2, Function.update_of_ne h1,
    show 2 * (z + 1) = 2 * z + 2 by ring]
  have hzeta : riemannZeta (z + 1) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre1
  have e1 : z + 1 - 1 = z := by ring
  have e2 : 2 * z + 2 - 1 = 2 * z + 1 := by ring
  rw [e1, e2]
  field_simp

/-! ## The one-sided measure and Landau's theorem -/

/-- The density `F(u) + C e^{-u/2}`, clipped at `0`. -/
def liouvilleExpDensity (C : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (liouvilleExpLog u + C * Real.exp (-u / 2))

theorem measurable_liouvilleExpDensity (C : ℝ) : Measurable (liouvilleExpDensity C) :=
  Measurable.real_toNNReal (continuous_liouvilleExpLog.measurable.add
    (measurable_const.mul (Real.measurable_exp.comp (measurable_id.neg.div_const 2))))

/-- `ν = (F(u) + C e^{-u/2}) du` on `(0, ∞)`. -/
def liouvilleExpMeasure (C : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (liouvilleExpDensity C u : ENNReal))

theorem liouvilleExpDensity_coe {C₀ C : ℝ} (hC : C₀ ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) {u : ℝ} (hu : 0 < u) :
    ((liouvilleExpDensity C u : ℝ)) = liouvilleExpLog u + C * Real.exp (-u / 2) := by
  unfold liouvilleExpDensity
  have h := hg u hu
  have hE := Real.exp_pos (-u / 2)
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem liouvilleExpDensity_le (C : ℝ) {u : ℝ} (hu : 0 < u) :
    ((liouvilleExpDensity C u : ℝ)) ≤ 1 + |C| + u := by
  unfold liouvilleExpDensity
  rw [Real.coe_toNNReal']
  have h1 := abs_liouvilleExpLog_le_of_nonneg hu.le
  have h2 : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : C * Real.exp (-u / 2) ≤ |C| := by
    calc C * Real.exp (-u / 2) ≤ |C| * Real.exp (-u / 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = |C| := mul_one _
  refine max_le ?_ (by positivity)
  linarith [le_abs_self (liouvilleExpLog u)]

theorem laplaceMass_liouvilleExpMeasure_ne_top (C : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    laplaceMass (liouvilleExpMeasure C) σ ≠ ⊤ := by
  unfold laplaceMass liouvilleExpMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleExpDensity C).coe_nnreal_ennreal hg]
  have hmaj : IntegrableOn (fun u : ℝ => (1 + |C|) * Real.exp (-σ * u) +
      (2 / σ) * Real.exp (-(σ / 2) * u)) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 hσ).const_mul _).add
      ((exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _)
  refine ne_top_of_le_ne_top hmaj.lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := liouvilleExpDensity_le C hu0
  have hu2 : u ≤ (2 / σ) * Real.exp ((σ / 2) * u) := by
    have h := Real.add_one_le_exp ((σ / 2) * u)
    have h' : (σ / 2) * u ≤ Real.exp ((σ / 2) * u) := by linarith
    calc u = (2 / σ) * ((σ / 2) * u) := by field_simp
      _ ≤ (2 / σ) * Real.exp ((σ / 2) * u) := mul_le_mul_of_nonneg_left h' (by positivity)
  have hE := Real.exp_pos (-σ * u)
  calc ((liouvilleExpDensity C u : ℝ)) * Real.exp (-σ * u) ≤ (1 + |C| + u) * Real.exp (-σ * u) :=
        mul_le_mul_of_nonneg_right h1 hE.le
    _ ≤ (1 + |C| + (2 / σ) * Real.exp ((σ / 2) * u)) * Real.exp (-σ * u) := by gcongr
    _ = (1 + |C|) * Real.exp (-σ * u) + (2 / σ) * Real.exp (-(σ / 2) * u) := by
        rw [add_mul, mul_assoc (2 / σ), ← Real.exp_add]; ring_nf

theorem laplaceMass_liouvilleExpMeasure_eq_top {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) {σ : ℝ}
    (hσ : σ ≤ -1 / 2) : laplaceMass (liouvilleExpMeasure C) σ = ⊤ := by
  unfold laplaceMass liouvilleExpMeasure
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleExpDensity C).coe_nnreal_ennreal hg', eq_top_iff]
  calc (⊤ : ENNReal) = ENNReal.ofReal 1 * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.ofReal_one, one_mul]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal 1 := by rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (liouvilleExpDensity C u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [liouvilleExpDensity_coe (by linarith) hg hu0]
        have h1 := hg u hu0
        have hE := Real.exp_pos (-u / 2)
        have hE2 := Real.exp_pos (-σ * u)
        have h2 : 1 ≤ Real.exp (-u / 2) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have h3 : Real.exp (-u / 2) ≤ liouvilleExpLog u + C * Real.exp (-u / 2) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h3 hE2.le]

theorem isAbscissa_liouvilleExpMeasure {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) :
    IsAbscissa (liouvilleExpMeasure C)
        (sInf {σ : ℝ | laplaceMass (liouvilleExpMeasure C) σ ≠ ⊤})
      ∧ -1 / 2 ≤ sInf {σ : ℝ | laplaceMass (liouvilleExpMeasure C) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (liouvilleExpMeasure C) σ ≠ ⊤} ≤ 1 := by
  set S := {σ : ℝ | laplaceMass (liouvilleExpMeasure C) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, -1 / 2 < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_liouvilleExpMeasure_eq_top hC hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨-1 / 2, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1 : ℝ) ∈ S := laplaceMass_liouvilleExpMeasure_ne_top C one_pos
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd h1S⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-- The continuation `Φ(z) = κ(z) - E(z) + C/(z + ½)`. -/
def liouvilleExpContinuation (C : ℝ) (z : ℂ) : ℂ :=
  liouvilleExpKernel z - liouvilleExpTail z + C / (z + 1 / 2)

theorem analyticAt_liouvilleExpContinuation (C : ℝ) {z : ℂ} (hz : -1 / 2 < z.re)
    (hZ : zetaResidueUnit (z + 1) ≠ 0) : AnalyticAt ℂ (liouvilleExpContinuation C) z := by
  have h2 : 2 * z + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hh : z + 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold liouvilleExpContinuation
  exact ((analyticAt_liouvilleExpKernel (by linarith) h2 hZ).sub
    (differentiable_liouvilleExpTail.analyticAt z)).add
    (analyticAt_const.div (analyticAt_id.add analyticAt_const) hh)

/-- On `Re z > 0` the complex transform of `ν` is `Φ(z)`. -/
theorem complexLaplace_liouvilleExpMeasure_eq {C₀ C : ℝ} (hC : C₀ ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) {z : ℂ} (hz : 0 < z.re) :
    complexLaplace (liouvilleExpMeasure C) z = liouvilleExpContinuation C z := by
  have hzh : 0 < (z + 1 / 2).re := by simp; linarith
  unfold complexLaplace liouvilleExpMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_liouvilleExpDensity C)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), liouvilleExpDensity C u • Complex.exp (-z * (u : ℂ))
      = cexp (-z * u) * (liouvilleExpLog u : ℂ) + (C : ℂ) * cexp (-(z + 1 / 2) * (u : ℂ)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, liouvilleExpDensity_coe hC hg hu]
    push_cast
    rw [show cexp (-(z + 1 / 2) * (u : ℂ)) = cexp (-(u : ℂ) / 2) * cexp (-z * (u : ℂ)) by
      rw [← Complex.exp_add]; congr 1; ring]
    ring
  have i1 := integrableOn_Ioi_liouvilleExpIntegrand hz
  have i2 : IntegrableOn (fun u : ℝ => (C : ℂ) * cexp (-(z + 1 / 2) * (u : ℂ))) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hzh).mono' ?_ ?_).const_mul _
    · exact (by fun_prop : Continuous fun u : ℝ => cexp (-(z + 1 / 2) * (u : ℂ))).aestronglyMeasurable
    · exact Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u)
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i1 i2, integral_const_mul,
    integral_cexp_neg_mul_Ioi hzh, integral_Ioi_liouvilleExpLog hz, Gamma_mul_LSeries_eq_kernel hz]
  unfold liouvilleExpContinuation
  ring

/-- **Landau: the abscissa of `ν` is `-½`.** -/
theorem abscissa_liouvilleExpMeasure_eq {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) :
    IsAbscissa (liouvilleExpMeasure C) (-1 / 2) := by
  obtain ⟨hc, hac, hc2⟩ := isAbscissa_liouvilleExpMeasure hC hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (liouvilleExpMeasure C) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hZ : zetaResidueUnit ((c : ℂ) + 1) ≠ 0 := by
      have := zetaResidueUnit_ofReal_ne_zero (t := c + 1) (by linarith)
      simpa using this
    have hcre : -1 / 2 < ((c : ℂ)).re := by simpa using hpos
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit (z + 1) ≠ 0 ∧ -1 / 2 < z.re :=
      (((analyticAt_zetaResidueUnit _).comp (analyticAt_id.add analyticAt_const)).continuousAt.eventually_ne
        hZ).and ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hcre)
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := liouvilleExpContinuation C) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2⟩ := hball hz
      exact analyticAt_liouvilleExpContinuation C h2 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (liouvilleExpMeasure C))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (liouvilleExpMeasure C) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (liouvilleExpMeasure C)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => liouvilleExpContinuation C (t : ℂ)) (Ioi c) := by
        intro t ht
        have ht' : c < t := ht
        have h1 : AnalyticAt ℂ (liouvilleExpContinuation C) (t : ℂ) := by
          refine analyticAt_liouvilleExpContinuation C (by simp; linarith) ?_
          have := zetaResidueUnit_ofReal_ne_zero (t := t + 1) (by linarith)
          simpa using this
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (2 : ℝ) ∈ Ioi c := by show c < 2; linarith
      have hfg : (fun t : ℝ => complexLaplace (liouvilleExpMeasure C) (t : ℂ)) =ᶠ[𝓝 (2 : ℝ)]
          (fun t : ℝ => liouvilleExpContinuation C (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)) fun t ht => ?_
        have ht1 : 0 < (t : ℂ).re := by simp; linarith [ht.1]
        exact complexLaplace_liouvilleExpMeasure_eq (by linarith) hg ht1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (liouvilleExpMeasure C) (σ : ℂ)
          = liouvilleExpContinuation C (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **The continuation identity on `Re z > -½`.**
`(∫ e^{-zu} dν + E(z) - C/(z+½)) (2z+1) Z(z+1) = Γ(z+1) Z(2z+2)`. -/
theorem liouvilleExp_continuation_identity {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u)
    {z : ℂ} (hz : -1 / 2 < z.re) :
    (complexLaplace (liouvilleExpMeasure C) z + liouvilleExpTail z - C / (z + 1 / 2))
      * ((2 * z + 1) * zetaResidueUnit (z + 1)) = Gamma (z + 1) * zetaResidueUnit (2 * z + 2) := by
  have hc := abscissa_liouvilleExpMeasure_eq hC hg
  set U : Set ℂ := {w : ℂ | -1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hneh : ∀ w ∈ U, w + 1 / 2 ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  set F : ℂ → ℂ := fun w => (complexLaplace (liouvilleExpMeasure C) w + liouvilleExpTail w
    - C / (w + 1 / 2)) * ((2 * w + 1) * zetaResidueUnit (w + 1)) with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    have h1 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    have h2 := differentiable_liouvilleExpTail w
    have h3 : DifferentiableAt ℂ (fun w : ℂ => (C : ℂ) / (w + 1 / 2)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _))
        (hneh w hw)
    have h4 : DifferentiableAt ℂ (fun w => (2 * w + 1) * zetaResidueUnit (w + 1)) w :=
      (((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)).mul
        ((analyticAt_zetaResidueUnit _).differentiableAt.comp w
          (differentiableAt_id.add (differentiableAt_const _)))
    exact (((h1.add h2).sub h3).mul h4).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ (fun w : ℂ => Gamma (w + 1) * zetaResidueUnit (2 * w + 2)) U :=
    fun w hw => ((analyticAt_Gamma_of_pos_re (by simp [hU] at hw ⊢; linarith)).comp
      (analyticAt_id.add analyticAt_const)).mul
      ((analyticAt_zetaResidueUnit _).comp ((analyticAt_const.mul analyticAt_id).add analyticAt_const))
  have h1U : (1 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : F =ᶠ[𝓝 (1 : ℂ)] fun w : ℂ => Gamma (w + 1) * zetaResidueUnit (2 * w + 2) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with w hw
    have hw0 : 0 < w.re := hw
    have h2 : 2 * w + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hZ : zetaResidueUnit (w + 1) ≠ 0 := zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
    simp only [hF]
    rw [complexLaplace_liouvilleExpMeasure_eq (by linarith) hg hw0, liouvilleExpContinuation]
    have hden : (2 * w + 1) * zetaResidueUnit (w + 1) ≠ 0 := mul_ne_zero h2 hZ
    have e : liouvilleExpKernel w * ((2 * w + 1) * zetaResidueUnit (w + 1)) =
        Gamma (w + 1) * zetaResidueUnit (2 * w + 2) := by
      unfold liouvilleExpKernel; exact div_mul_cancel₀ _ hden
    linear_combination e
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt _).isPreconnected h1U hev
  exact hEq hz

/-- **A one-sided `√t` bound for `J` near `0` implies the Riemann hypothesis** (logarithmic form). -/
theorem riemannHypothesis_of_liouvilleExpLog_lower {C₀ : ℝ}
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) : RiemannHypothesis := by
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro w hw hzero
  have hz : -1 / 2 < (w - 1).re := by simp; linarith
  have hid := liouvilleExp_continuation_identity (le_refl (C₀ + 1)) hg hz
  rw [show w - 1 + 1 = w by ring, hzero, mul_zero, mul_zero] at hid
  have hG : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hZ2 : zetaResidueUnit (2 * (w - 1) + 2) ≠ 0 := by
    rw [show 2 * (w - 1) + 2 = 2 * w by ring]
    exact zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
  exact mul_ne_zero hG hZ2 hid.symm

/-! ## Simplicity of critical zeros -/

/-- `r ∫ e^{(½ - r)u} dν` stays bounded as `r ↓ 0`. -/
theorem exists_bound_mul_laplaceReal {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) :
    ∃ B : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0, r * laplaceReal (liouvilleExpMeasure C) (-1 / 2 + r) ≤ B := by
  set q : ℝ → ℂ := fun r => Gamma ((1 / 2 + r : ℝ) : ℂ) * zetaResidueUnit (1 + 2 * (r : ℂ)) /
    (2 * zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ)) with hq
  have hZh : zetaResidueUnit ((1 / 2 : ℝ) : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero (by norm_num)
  have hqc : ContinuousAt q 0 := by
    have hG : ContinuousAt (fun r : ℝ => Gamma ((1 / 2 + r : ℝ) : ℂ)) 0 := by
      have h := (analyticAt_Gamma_of_pos_re (w := ((1 / 2 + 0 : ℝ) : ℂ)) (by simp)).continuousAt
      exact ContinuousAt.comp (g := Gamma) (f := fun r : ℝ => ((1 / 2 + r : ℝ) : ℂ)) h
        (by fun_prop)
    have hZ1 : ContinuousAt (fun r : ℝ => zetaResidueUnit (1 + 2 * (r : ℂ))) 0 :=
      ContinuousAt.comp (g := zetaResidueUnit) (f := fun r : ℝ => 1 + 2 * (r : ℂ))
        (analyticAt_zetaResidueUnit _).continuousAt (by fun_prop)
    have hZ2 : ContinuousAt (fun r : ℝ => zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ)) 0 :=
      ContinuousAt.comp (g := zetaResidueUnit) (f := fun r : ℝ => ((1 / 2 + r : ℝ) : ℂ))
        (analyticAt_zetaResidueUnit _).continuousAt (by fun_prop)
    refine (hG.mul hZ1).div (continuousAt_const.mul hZ2) ?_
    simpa using mul_ne_zero two_ne_zero hZh
  have hEc : ContinuousAt (fun r : ℝ => liouvilleExpTail ((-1 / 2 + r : ℝ) : ℂ)) 0 :=
    (differentiable_liouvilleExpTail.continuous.comp
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))).continuousAt
  have hbq := (hqc.norm).eventually (gt_mem_nhds (lt_add_one ‖q 0‖))
  have hbE := (hEc.norm).eventually (gt_mem_nhds (lt_add_one ‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖))
  refine ⟨‖q 0‖ + 1 + (‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖ + 1) + |C|, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hbq, nhdsWithin_le_nhds hbE, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r h1 h2 hr hr1
  have hr0 : 0 < r := hr
  have hr1' : r < 1 := hr1
  set z : ℂ := ((-1 / 2 + r : ℝ) : ℂ) with hz
  have hzre : -1 / 2 < z.re := by simp [hz]; linarith
  have hid := liouvilleExp_continuation_identity hC hg hzre
  have hz1 : z + 1 = ((1 / 2 + r : ℝ) : ℂ) := by simp [hz]; ring
  have hz2 : 2 * z + 1 = 2 * (r : ℂ) := by simp [hz]; ring
  have hz3 : 2 * z + 2 = 1 + 2 * (r : ℂ) := by simp [hz]; ring
  have hzh : z + 1 / 2 = (r : ℂ) := by simp [hz]; ring
  rw [hz1, hz2, hz3, hzh] at hid
  have hZ : zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero (by linarith)
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hL : (r : ℂ) * complexLaplace (liouvilleExpMeasure C) z =
      q r - (r : ℂ) * liouvilleExpTail z + C := by
    have hq' : q r = Gamma ((1 / 2 + r : ℝ) : ℂ) * zetaResidueUnit (1 + 2 * (r : ℂ)) /
        (2 * zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ)) := rfl
    rw [hq']
    generalize Gamma ((1 / 2 + r : ℝ) : ℂ) = Gw at hid ⊢
    generalize zetaResidueUnit (1 + 2 * (r : ℂ)) = Z1 at hid ⊢
    generalize hZw : zetaResidueUnit ((1 / 2 + r : ℝ) : ℂ) = Zw at hid hZ ⊢
    generalize complexLaplace (liouvilleExpMeasure C) z = CL at hid ⊢
    generalize liouvilleExpTail z = E at hid ⊢
    generalize hR : (r : ℂ) = R at hid hrc ⊢
    have hden : 2 * R * Zw ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hrc) hZ
    have h' := eq_div_of_mul_eq hden hid
    have hCL : CL = Gw * Z1 / (2 * R * Zw) - E + (C : ℂ) / R := by linear_combination h'
    rw [hCL]
    field_simp
  rw [complexLaplace_ofReal] at hL
  have hLr := congrArg Complex.re hL
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.add_re] at hLr
  have hqr : (q r).re ≤ ‖q 0‖ + 1 := (Complex.re_le_norm _).trans h1.le
  have hEr : -(r * (liouvilleExpTail z).re) ≤ ‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖ + 1 := by
    have : |(liouvilleExpTail z).re| ≤ ‖liouvilleExpTail z‖ := Complex.abs_re_le_norm _
    have h2' : ‖liouvilleExpTail z‖ < ‖liouvilleExpTail ((-1 / 2 + 0 : ℝ) : ℂ)‖ + 1 := h2
    have hrabs : r * |(liouvilleExpTail z).re| ≤ |(liouvilleExpTail z).re| :=
      mul_le_of_le_one_left (abs_nonneg _) hr1'.le
    nlinarith [neg_abs_le (liouvilleExpTail z).re, abs_nonneg (liouvilleExpTail z).re]
  have hCr : (C : ℂ).re = C := Complex.ofReal_re C
  linarith [le_abs_self C]

/-- **A one-sided bound for `J` makes every zero on the critical line simple.** -/
theorem liouvilleExp_zero_simple {C₀ C : ℝ} (hC : C₀ + 1 ≤ C)
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) {m : ℕ}
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = (z - ρ) ^ m • G z) : m = 1 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have := hfac.self_of_nhds
      rw [h, pow_zero, one_smul, hρ0] at this
      exact hG0 this.symm
    · exact h
  by_contra hm1
  have hm2 : 2 ≤ m := by omega
  obtain ⟨B, hB⟩ := exists_bound_mul_laplaceReal hC hg
  set γ : ℝ := |ρ.im| with hγ
  have hγ0 : 0 < γ := abs_pos.mpr hρim
  have h2ρ : 2 * ρ ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hρim this
  have hZ2 : zetaResidueUnit (2 * ρ) ≠ 0 := by
    have hre : (2 * ρ).re = 1 := by simp [hρre]
    rw [zetaResidueUnit, Function.update_of_ne h2ρ]
    exact mul_ne_zero (sub_ne_zero.mpr h2ρ) (riemannZeta_ne_zero_of_one_le_re hre.ge)
  have hGam : Gamma ρ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hρre]; norm_num)
  set A₀ : ℝ := ‖Gamma ρ * zetaResidueUnit (2 * ρ)‖ with hA₀
  have hA₀pos : 0 < A₀ := norm_pos_iff.mpr (mul_ne_zero hGam hZ2)
  have htend : Tendsto (fun r : ℝ => ρ + r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + r) (𝓝 (0 : ℝ)) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  -- left side tends to `A₀`
  have hLt : Tendsto (fun r : ℝ => ‖Gamma (ρ + r) * zetaResidueUnit (2 * (ρ + r))‖) (𝓝[>] 0)
      (𝓝 A₀) := by
    have hc : ContinuousAt (fun w : ℂ => Gamma w * zetaResidueUnit (2 * w)) ρ :=
      ((analyticAt_Gamma_of_pos_re (by rw [hρre]; norm_num)).mul
        ((analyticAt_zetaResidueUnit _).comp (analyticAt_const.mul analyticAt_id))).continuousAt
    exact (hc.tendsto.comp htend).norm
  -- right side tends to `0`
  set K₁ : ℝ := ‖liouvilleExpTail (ρ - 1)‖ + 1 with hK₁
  have hEc : ContinuousAt liouvilleExpTail (ρ - 1) := differentiable_liouvilleExpTail.continuous.continuousAt
  have hEt : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖liouvilleExpTail (ρ - 1 + r)‖ ≤ K₁ := by
    have h' : Tendsto (fun r : ℝ => ρ - 1 + r) (𝓝[>] (0 : ℝ)) (𝓝 (ρ - 1)) := by
      have := htend.sub_const 1
      simpa [sub_add_eq_add_sub] using this
    exact (h'.eventually (hEc.norm.eventually (gt_mem_nhds (lt_add_one _)))).mono fun r h => h.le
  set K₂ : ℝ := ‖2 * ρ - 1‖ + 1 with hK₂
  set K₃ : ℝ := ‖G ρ‖ + 1 with hK₃
  have hR : Tendsto (fun r : ℝ => r ^ (m - 1) * ((|B| + r * K₁ + r * (|C| / γ)) * (K₂ * K₃)))
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => r ^ (m - 1) * ((|B| + r * K₁ + r * (|C| / γ)) * (K₂ * K₃)))
        (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (m - 1) * ((|B| + 0 * K₁ + 0 * (|C| / γ)) * (K₂ * K₃)))) :=
      ((continuous_pow _).mul ((((continuous_const.add (continuous_id.mul continuous_const)).add
        (continuous_id.mul continuous_const))).mul continuous_const)).tendsto 0
    rw [zero_pow (by omega), zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hfac' := htend.eventually hfac
  have hGc : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖G (ρ + r)‖ ≤ K₃ :=
    (htend.eventually (hGan.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _)))).mono
      fun r h => h.le
  have h2c : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖2 * (ρ + r) - 1‖ ≤ K₂ :=
    (htend.eventually (((continuous_const.mul continuous_id).sub continuous_const).norm.continuousAt
      (x := ρ) |>.eventually (gt_mem_nhds (lt_add_one _)))).mono fun r h => h.le
  have hle : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖Gamma (ρ + r) * zetaResidueUnit (2 * (ρ + r))‖ ≤
      r ^ (m - 1) * ((|B| + r * K₁ + r * (|C| / γ)) * (K₂ * K₃)) := by
    filter_upwards [hfac', hGc, h2c, hEt, hB, self_mem_nhdsWithin] with r hr hG hr2 hE hb hr0
    have hr0' : 0 < r := hr0
    set z : ℂ := ρ - 1 + r with hz
    have hzre : -1 / 2 < z.re := by simp [hz, hρre]; linarith
    have hid := liouvilleExp_continuation_identity hC hg hzre
    have e1 : z + 1 = ρ + r := by rw [hz]; ring
    have e2 : 2 * z + 2 = 2 * (ρ + r) := by rw [hz]; ring
    have e3 : 2 * z + 1 = 2 * (ρ + r) - 1 := by rw [hz]; ring
    rw [e1, e2, e3, hr, show ρ + (r : ℂ) - ρ = (r : ℂ) by ring, smul_eq_mul] at hid
    set H : ℂ := complexLaplace (liouvilleExpMeasure C) z + liouvilleExpTail z - C / (z + 1 / 2)
      with hH
    have hnorm := congrArg norm hid
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0'] at hnorm
    have hzim : (z + 1 / 2).im = ρ.im := by simp [hz]
    have hγle : γ ≤ ‖z + 1 / 2‖ := by
      have := Complex.abs_im_le_norm (z + 1 / 2); rw [hzim] at this; exact this
    have hCL : ‖complexLaplace (liouvilleExpMeasure C) z‖ ≤
        laplaceReal (liouvilleExpMeasure C) (-1 / 2 + r) := by
      have := norm_complexLaplace_le (liouvilleExpMeasure C) z
      have hre : z.re = -1 / 2 + r := by simp [hz, hρre]; ring
      rw [hre] at this
      exact this
    have hlapnn : 0 ≤ laplaceReal (liouvilleExpMeasure C) (-1 / 2 + r) :=
      integral_nonneg fun u => (Real.exp_pos _).le
    have hCz : ‖(C : ℂ) / (z + 1 / 2)‖ ≤ |C| / γ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg C) hγ0 hγle
    have hEz : ‖liouvilleExpTail z‖ ≤ K₁ := by rw [hz]; exact hE
    have hHle : r * ‖H‖ ≤ |B| + r * K₁ + r * (|C| / γ) := by
      have h1 : ‖H‖ ≤ laplaceReal (liouvilleExpMeasure C) (-1 / 2 + r) + K₁ + |C| / γ := by
        have := norm_sub_le (complexLaplace (liouvilleExpMeasure C) z + liouvilleExpTail z)
          ((C : ℂ) / (z + 1 / 2))
        have := norm_add_le (complexLaplace (liouvilleExpMeasure C) z) (liouvilleExpTail z)
        rw [hH]; linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hr0'.le
      have h3 : r * laplaceReal (liouvilleExpMeasure C) (-1 / 2 + r) ≤ |B| := hb.trans (le_abs_self B)
      nlinarith
    have hpow : r ^ m = r ^ (m - 1) * r := by rw [← pow_succ]; congr 1; omega
    rw [← hnorm, hpow]
    have hK₂0 : 0 ≤ K₂ := by positivity
    have hK₃0 : 0 ≤ K₃ := by positivity
    calc ‖H‖ * (‖2 * (ρ + r) - 1‖ * (r ^ (m - 1) * r * ‖G (ρ + r)‖))
        = r ^ (m - 1) * ((r * ‖H‖) * (‖2 * (ρ + r) - 1‖ * ‖G (ρ + r)‖)) := by ring
      _ ≤ r ^ (m - 1) * ((|B| + r * K₁ + r * (|C| / γ)) * (K₂ * K₃)) := by
          gcongr
  have := le_of_tendsto_of_tendsto hLt hR hle
  linarith

/-- **A one-sided `√t` bound for `J` makes every critical zero simple** (logarithmic form). -/
theorem deriv_zetaResidueUnit_ne_zero_of_liouvilleExpLog_lower {C₀ : ℝ}
    (hg : ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u) {ρ : ℂ}
    (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) :
    deriv zetaResidueUnit ρ ≠ 0 := by
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
    intro hzero
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_zetaResidueUnit z) isPreconnected_univ (mem_univ ρ) hzero
    have := hall (mem_univ (1 : ℂ))
    simp at this
  obtain ⟨m, G, hGan, hG0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  have hm := liouvilleExp_zero_simple (le_refl (C₀ + 1)) hg hρre hρim hρ0 hGan hG0 hfac
  rw [hm] at hfac
  have hd : HasDerivAt (fun z => (z - ρ) ^ 1 • G z) (G ρ) ρ := by
    have h1 : HasDerivAt (fun z : ℂ => (z - ρ) ^ 1) 1 ρ := by
      simpa using (hasDerivAt_id ρ).sub_const ρ
    have h2 := h1.mul hGan.differentiableAt.hasDerivAt
    refine h2.congr_deriv ?_
    simp
  rw [(hd.congr_of_eventuallyEq hfac).deriv]
  exact hG0

/-! ## The statement in the variable `t` -/

theorem exists_liouvilleExpLog_lower {C t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → -(C * Real.sqrt t) ≤ liouvilleExpSum t) :
    ∃ C₀ : ℝ, ∀ u, 0 < u → -(C₀ * Real.exp (-u / 2)) ≤ liouvilleExpLog u := by
  set B : ℝ := 1 + |Real.log t₀| with hB
  refine ⟨max C 0 + B / Real.sqrt t₀, fun u hu => ?_⟩
  set t := Real.exp (-u) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsq : Real.sqrt t = Real.exp (-u / 2) := by
    rw [ht, show Real.exp (-u) = Real.exp (-u / 2) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have hE := Real.exp_pos (-u / 2)
  have hsq0 : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr ht₀
  have hBn : 0 ≤ B := by positivity
  unfold liouvilleExpLog
  rw [← hsq]
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  rcases le_or_gt t t₀ with htt | htt
  · have h1 := h t ht0 htt
    have h2 : -(max C 0 * Real.sqrt t) ≤ -(C * Real.sqrt t) := by
      have := mul_le_mul_of_nonneg_right (le_max_left C 0) hst; linarith
    have h3 : 0 ≤ B / Real.sqrt t₀ * Real.sqrt t := by positivity
    nlinarith
  · have hJ := abs_liouvilleExpSum_le_small ht0 ht1
    have hlog : Real.log (1 / t) ≤ |Real.log t₀| := by
      rw [one_div, Real.log_inv]
      have := Real.log_le_log ht₀ htt.le
      linarith [neg_abs_le (Real.log t₀), le_abs_self (Real.log t₀)]
    have hJ' : -B ≤ liouvilleExpSum t := by
      have := neg_abs_le (liouvilleExpSum t); rw [hB]; linarith
    have hratio : 1 ≤ Real.sqrt t / Real.sqrt t₀ := by
      rw [le_div_iff₀ hsq0, one_mul]; exact Real.sqrt_le_sqrt htt.le
    have h4 : B ≤ B / Real.sqrt t₀ * Real.sqrt t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsq0]
      nlinarith [Real.sqrt_le_sqrt htt.le]
    have h5 : 0 ≤ max C 0 * Real.sqrt t := mul_nonneg (le_max_right C 0) hst
    nlinarith

/-- **A one-sided `√t` bound for the exponential Liouville sum implies the Riemann hypothesis.**
If `Σ λ(n) e^{-nt}/n ≥ -C√t` for `0 < t ≤ t₀`, then RH holds. -/
theorem riemannHypothesis_of_liouvilleExpSum_lower {C t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → -(C * Real.sqrt t) ≤ liouvilleExpSum t) : RiemannHypothesis := by
  obtain ⟨C₀, hg⟩ := exists_liouvilleExpLog_lower ht₀ h
  exact riemannHypothesis_of_liouvilleExpLog_lower hg

/-- **… and makes every zero on the critical line simple.** -/
theorem deriv_zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower {C t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → -(C * Real.sqrt t) ≤ liouvilleExpSum t) {ρ : ℂ}
    (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) :
    deriv zetaResidueUnit ρ ≠ 0 := by
  obtain ⟨C₀, hg⟩ := exists_liouvilleExpLog_lower ht₀ h
  exact deriv_zetaResidueUnit_ne_zero_of_liouvilleExpLog_lower hg hρre hρim hρ0

end

end RHTower
