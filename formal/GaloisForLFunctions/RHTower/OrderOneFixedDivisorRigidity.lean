/-
# Order-one fixed-divisor rigidity

Two entire functions with the same divisor and subquadratic Nevanlinna proximity differ by the
exponential of an affine function, and if both are even they differ by a constant.  With one
normalization value they are equal.

The proof is the value-distribution form of Hadamard uniqueness.  Writing `H = G/F` for the entire
zero-free quotient, the first main theorem bounds `T(r, F⁻¹)` by `T(r, F)` up to a constant, and
submultiplicativity of the characteristic gives

`m(r, H) = T(r, H) ≤ T(r, G) + T(r, F⁻¹) ≤ m(r, G) + m(r, F) + O(1) = o(r²)`,

after which a zero-free entire function of subquadratic proximity has an affine logarithm.  The
growth hypothesis is supplied in practice by an order-one envelope `exp(C(1+r)log(2+r))`, which
forces `m(r, F) = o(r²)` because `log r = o(r)`.
-/
import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.EntireHasLog
import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.NevanlinnaMaxModulusBridge
import GaloisForLFunctions.HTGeometry.QuotientProximityBound

noncomputable section

open Complex Filter Topology Metric ValueDistribution Asymptotics
open GaloisForLFunctions.Nevanlinna GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.QuotientProximity

namespace RHTower.OrderOneRigidity

/-! ## Order-one growth gives subquadratic proximity -/

theorem isLittleO_orderOneEnvelope (C : ℝ) :
    (fun r : ℝ => C * (1 + r) * Real.log (2 + r)) =o[atTop] fun r : ℝ => r ^ (2 : ℕ) := by
  have hlog : (fun r : ℝ => Real.log (2 + r)) =o[atTop] fun r : ℝ => r := by
    have h1 : (fun r : ℝ => Real.log (2 + r)) =o[atTop] fun r : ℝ => 2 + r := by
      have := Real.isLittleO_log_id_atTop.comp_tendsto
        (tendsto_atTop_add_const_left atTop (2 : ℝ) tendsto_id)
      exact this
    refine h1.trans_isBigO ?_
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  have hlin : (fun r : ℝ => C * (1 + r)) =O[atTop] fun r : ℝ => r := by
    refine IsBigO.of_bound (|C| * 2) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ r),
      abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + r)]
    nlinarith [abs_nonneg C]
  have := hlin.mul_isLittleO hlog
  refine this.congr' (Filter.Eventually.of_forall (fun r => by ring)) ?_
  filter_upwards with r
  ring

/-- **Order-one growth gives subquadratic proximity.**  A growth envelope `exp(C(1+r)log(2+r))`,
the unconditional envelope of an entire function of order at most one, forces the Nevanlinna
proximity to be `o(r²)`. -/
theorem proximity_isLittleO_sq_of_growth {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : Differentiable ℂ F)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    proximity F ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ) := by
  have hFan : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hF
  have hbnd : ∀ r : ℝ, 1 ≤ r →
      proximity F ⊤ r ≤ C * (1 + r) * Real.log (2 + r) := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := by linarith
    have hmer : MeromorphicOn F (sphere (0 : ℂ) r) := fun z _ => (hFan z (Set.mem_univ z)).meromorphicAt
    have hM : ∀ z : ℂ, ‖z‖ = r → ‖F z‖ ≤ Real.exp (C * (1 + r) * Real.log (2 + r)) := by
      intro z hz
      have := hbound z
      rwa [hz] at this
    refine le_trans (proximity_top_le_posLog_of_norm hr0 hmer hM) ?_
    have hnn : 0 ≤ C * (1 + r) * Real.log (2 + r) := by
      have : (0 : ℝ) ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
      have h1 : (0 : ℝ) ≤ C * (1 + r) := by positivity
      positivity
    rw [Real.posLog, Real.log_exp]
    exact max_le hnn le_rfl
  have hmaj := isLittleO_orderOneEnvelope C
  refine IsBigO.trans_isLittleO ?_ hmaj
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hnn := proximity_nonneg_of_entire hFan hr
  have hle := hbnd r hr
  have hmajnn : 0 ≤ C * (1 + r) * Real.log (2 + r) := by
    have hlog : (0 : ℝ) ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
    have h1 : (0 : ℝ) ≤ C * (1 + r) := by positivity
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hmajnn, one_mul]
  exact hle

/-! ## The quotient inherits subquadratic proximity -/

theorem proximity_isLittleO_sq_of_entire_quotient
    {F G H : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (hH : Differentiable ℂ H)
    (hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤)
    (hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤)
    (hfac : ∀ z, G z = H z * F z)
    (hproxF : proximity F ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ))
    (hproxG : proximity G ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ)) :
    proximity H ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ) := by
  have hFan : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hF
  have hGan : AnalyticOnNhd ℂ G Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hG
  have hHan : AnalyticOnNhd ℂ H Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hH
  obtain ⟨K, hbnd⟩ := proximity_quotient_le hFan hGan hHan hFord hGord hfac
  rw [isLittleO_iff]
  intro c hc
  have hFo := (isLittleO_iff.mp hproxF) (c := c / 3) (by linarith)
  have hGo := (isLittleO_iff.mp hproxG) (c := c / 3) (by linarith)
  have hKo : ∀ᶠ r : ℝ in atTop, K ≤ (c / 3) * r ^ (2 : ℕ) := by
    have htend : Tendsto (fun r : ℝ => (c / 3) * r ^ (2 : ℕ)) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop (by linarith) ?_
      exact tendsto_pow_atTop (by norm_num)
    exact htend.eventually_ge_atTop K
  filter_upwards [hFo, hGo, hKo, eventually_ge_atTop (1 : ℝ)] with r hf hg hk hr
  have hnn := proximity_nonneg_of_entire hHan hr
  have hle := hbnd r hr
  have hrsq : ‖(r : ℝ) ^ (2 : ℕ)‖ = r ^ (2 : ℕ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, hrsq]
  rw [Real.norm_eq_abs, hrsq] at hf hg
  have hFabs : proximity F ⊤ r ≤ c / 3 * r ^ (2 : ℕ) := le_trans (le_abs_self _) hf
  have hGabs : proximity G ⊤ r ≤ c / 3 * r ^ (2 : ℕ) := le_trans (le_abs_self _) hg
  linarith

/-! ## Order-one fixed-divisor rigidity -/

/-- **Order-one fixed-divisor rigidity.**  Two entire functions of subquadratic proximity whose
quotient is entire and zero-free differ by the exponential of an affine function. -/
theorem exists_expAffine_of_entire_quotient
    {F G H : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (hH : Differentiable ℂ H)
    (hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤)
    (hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤)
    (hHne : ∀ z, H z ≠ 0)
    (hfac : ∀ z, G z = H z * F z)
    (hproxF : proximity F ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ))
    (hproxG : proximity G ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ)) :
    ∃ a b : ℂ, ∀ z, H z = Complex.exp (a * z + b) := by
  obtain ⟨g, hg, hexp⟩ := entire_nonvanishing_has_log H hH hHne
  have hprox := proximity_isLittleO_sq_of_entire_quotient hF hG hH hFord hGord hfac hproxF hproxG
  have haff := entire_log_affine_of_proximity_isLittleO_sq H g hg hexp hprox
  refine ⟨deriv g 0, g 0, fun z => ?_⟩
  rw [hexp z, haff z]
  ring_nf

/-- **Evenness removes the linear coefficient.**  If both functions are even, the quotient is
constant. -/
theorem exists_const_of_even_entire_quotient
    {F G H : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (hH : Differentiable ℂ H)
    (hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤)
    (hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤)
    (hHne : ∀ z, H z ≠ 0)
    (hfac : ∀ z, G z = H z * F z)
    (hHeven : ∀ z, H (-z) = H z)
    (hproxF : proximity F ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ))
    (hproxG : proximity G ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ)) :
    ∀ z, H z = H 0 := by
  obtain ⟨a, b, hab⟩ :=
    exists_expAffine_of_entire_quotient hF hG hH hFord hGord hHne hfac hproxF hproxG
  have ha : a = 0 := by
    have hderiv : ∀ z : ℂ, Complex.exp (a * (-z) + b) = Complex.exp (a * z + b) := by
      intro z
      rw [← hab (-z), ← hab z, hHeven z]
    have hone : ∀ z : ℂ, Complex.exp (2 * a * z) = 1 := by
      intro z
      have h := hderiv (-z)
      have h2 : Complex.exp (a * z + b) = Complex.exp (a * (-z) + b) := (hderiv z).symm
      have h3 : Complex.exp (a * z + b) / Complex.exp (a * (-z) + b) = 1 := by
        rw [← h2]
        exact div_self (Complex.exp_ne_zero _)
      rw [← Complex.exp_sub] at h3
      have h4 : a * z + b - (a * (-z) + b) = 2 * a * z := by ring
      rwa [h4] at h3
    have hd : HasDerivAt (fun z : ℂ => Complex.exp (2 * a * z)) (Complex.exp (2 * a * 0) * (2 * a)) 0 := by
      have hb : HasDerivAt (fun z : ℂ => 2 * a * z) (2 * a) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul (2 * a)
      simpa using hb.cexp
    have hconst : HasDerivAt (fun z : ℂ => Complex.exp (2 * a * z)) 0 0 := by
      have hfun : (fun z : ℂ => Complex.exp (2 * a * z)) = fun _ => (1 : ℂ) := funext hone
      rw [hfun]
      exact hasDerivAt_const 0 1
    have huniq := hd.unique hconst
    simp only [mul_zero, Complex.exp_zero, one_mul] at huniq
    have : (2 : ℂ) * a = 0 := huniq
    simpa using this
  intro z
  rw [hab z, hab 0, ha]
  ring_nf

/-- **The canonical order-one representative is unique.**  Fixed divisor, subquadratic proximity,
evenness, and one normalization value leave no gauge freedom. -/
theorem eq_of_even_entire_quotient
    {F G H : ℂ → ℂ} {z₀ : ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (hH : Differentiable ℂ H)
    (hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤)
    (hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤)
    (hHne : ∀ z, H z ≠ 0)
    (hfac : ∀ z, G z = H z * F z)
    (hHeven : ∀ z, H (-z) = H z)
    (hproxF : proximity F ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ))
    (hproxG : proximity G ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ))
    (hFz₀ : F z₀ ≠ 0) (hnorm : G z₀ = F z₀) :
    ∀ z, G z = F z := by
  have hconst :=
    exists_const_of_even_entire_quotient hF hG hH hFord hGord hHne hfac hHeven hproxF hproxG
  have hH0 : H 0 = 1 := by
    have h : H 0 * F z₀ = 1 * F z₀ := by
      rw [one_mul, ← hconst z₀, ← hfac z₀, hnorm]
    exact mul_right_cancel₀ hFz₀ h
  intro z
  rw [hfac z, hconst z, hH0, one_mul]

end RHTower.OrderOneRigidity
