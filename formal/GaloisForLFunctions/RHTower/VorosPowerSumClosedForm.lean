import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.JetTotalDerivation
import GaloisForLFunctions.RHTower.BohrGeneratorAxisMode

/-!
# The Voros power sums: closed form and the Li/secular change of basis
-/

namespace GaloisForLFunctions.VorosClosedForm

open Complex GaloisForLFunctions

noncomputable section

/-! ## The simple pole at `1` -/

theorem iteratedDeriv_inv_sub_one (m : ℕ) :
    ∀ s : ℂ, s ≠ 1 → iteratedDeriv m (fun z : ℂ => 1 / (z - 1)) s
      = (-1) ^ m * (m.factorial : ℂ) / (s - 1) ^ (m + 1) := by
  induction m with
  | zero =>
      intro s _
      simp
  | succ m ih =>
      intro s hs
      have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
      have hev : iteratedDeriv m (fun z : ℂ => 1 / (z - 1))
          =ᶠ[nhds s] fun z : ℂ => (-1) ^ m * (m.factorial : ℂ) / (z - 1) ^ (m + 1) := by
        filter_upwards [hopen.mem_nhds hs] with z hz
        exact ih z hz
      have hsub : (s - 1) ≠ 0 := sub_ne_zero.mpr hs
      have hpow : ((s - 1) ^ (m + 1)) ≠ 0 := pow_ne_zero _ hsub
      have hbase : HasDerivAt (fun z : ℂ => (z - 1) ^ (m + 1))
          (((m + 1 : ℕ) : ℂ) * (s - 1) ^ (m + 1 - 1) * 1) s :=
        ((hasDerivAt_id s).sub_const (1 : ℂ)).pow (m + 1)
      have hdiv := (hasDerivAt_const s ((-1 : ℂ) ^ m * (m.factorial : ℂ))).div hbase hpow
      have hval : ((0 : ℂ) * (s - 1) ^ (m + 1) - (-1 : ℂ) ^ m * (m.factorial : ℂ) *
            (((m + 1 : ℕ) : ℂ) * (s - 1) ^ (m + 1 - 1) * 1)) / ((s - 1) ^ (m + 1)) ^ 2
          = (-1) ^ (m + 1) * ((m + 1).factorial : ℂ) / (s - 1) ^ (m + 1 + 1) := by
        rw [Nat.add_sub_cancel, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      have hdiv2 : HasDerivAt
          (fun z : ℂ => (-1 : ℂ) ^ m * (m.factorial : ℂ) / (z - 1) ^ (m + 1))
          (((0 : ℂ) * (s - 1) ^ (m + 1) - (-1 : ℂ) ^ m * (m.factorial : ℂ) *
            (((m + 1 : ℕ) : ℂ) * (s - 1) ^ (m + 1 - 1) * 1)) / ((s - 1) ^ (m + 1)) ^ 2) s := hdiv
      rw [iteratedDeriv_succ, hev.deriv_eq, hdiv2.deriv, hval]

/-! ## The digamma half-shift -/

theorem contDiffAt_digamma_top {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    ContDiffAt ℂ (⊤ : ℕ∞) Complex.digamma x := by
  rw [contDiffAt_infty]
  intro n
  exact contDiffAt_digamma_n x hx n

theorem offPoles_of_re_pos {w : ℂ} (hw : 0 < w.re) : ∀ m : ℕ, w ≠ -(m : ℂ) := by
  intro m hm
  rw [hm] at hw
  simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at hw
  exact absurd hw (not_lt.mpr (Nat.cast_nonneg m))

theorem differentiableAt_iteratedDeriv_digamma_of_re_pos {x : ℂ} (hx : 0 < x.re) (n : ℕ) :
    DifferentiableAt ℂ (iteratedDeriv n Complex.digamma) x :=
  HTGeometry.differentiableAt_iteratedDeriv_of_contDiffAt
    (U := {z : ℂ | 0 < z.re}) (isOpen_lt continuous_const Complex.continuous_re)
    (fun w hw => contDiffAt_digamma_top (offPoles_of_re_pos hw)) hx n

end

end GaloisForLFunctions.VorosClosedForm

namespace GaloisForLFunctions.VorosClosedForm

open Complex GaloisForLFunctions

noncomputable section

theorem hasDerivAt_iteratedDeriv_digamma {x : ℂ} (hx : 0 < x.re) (n : ℕ) :
    HasDerivAt (iteratedDeriv n Complex.digamma) (iteratedDeriv (n + 1) Complex.digamma x) x := by
  have hd := (differentiableAt_iteratedDeriv_digamma_of_re_pos hx n).hasDerivAt
  rwa [← iteratedDeriv_succ] at hd

theorem isOpen_halfShiftDomain : IsOpen {s : ℂ | 0 < (1 + s / 2).re} := by
  refine isOpen_lt continuous_const ?_
  fun_prop

/-- **The half-shifted digamma jets.**  `d^m/ds^m ψ(1 + s/2) = 2^{-m} ψ^{(m)}(1 + s/2)`. -/
theorem iteratedDeriv_digamma_halfShift (m : ℕ) :
    ∀ s : ℂ, 0 < (1 + s / 2).re →
      iteratedDeriv m (fun z : ℂ => Complex.digamma (1 + z / 2)) s
        = (1 / 2 : ℂ) ^ m * iteratedDeriv m Complex.digamma (1 + s / 2) := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
      intro s hs
      have hev : iteratedDeriv m (fun z : ℂ => Complex.digamma (1 + z / 2))
          =ᶠ[nhds s] fun z : ℂ => (1 / 2 : ℂ) ^ m * iteratedDeriv m Complex.digamma (1 + z / 2) := by
        filter_upwards [isOpen_halfShiftDomain.mem_nhds hs] with z hz
        exact ih z hz
      have haff : HasDerivAt (fun z : ℂ => 1 + z / 2) (1 / 2 : ℂ) s := by
        simpa using ((hasDerivAt_id s).div_const 2).const_add 1
      have hinner : HasDerivAt (iteratedDeriv m Complex.digamma)
          (iteratedDeriv (m + 1) Complex.digamma (1 + s / 2)) (1 + s / 2) :=
        hasDerivAt_iteratedDeriv_digamma hs m
      have hcomp : HasDerivAt (fun z : ℂ => iteratedDeriv m Complex.digamma (1 + z / 2))
          (iteratedDeriv (m + 1) Complex.digamma (1 + s / 2) * (1 / 2 : ℂ)) s := by
        have h := HasDerivAt.comp s hinner haff
        exact h
      have hfull : HasDerivAt
          (fun z : ℂ => (1 / 2 : ℂ) ^ m * iteratedDeriv m Complex.digamma (1 + z / 2))
          ((1 / 2 : ℂ) ^ m * (iteratedDeriv (m + 1) Complex.digamma (1 + s / 2) * (1 / 2 : ℂ))) s :=
        hcomp.const_mul _
      rw [iteratedDeriv_succ, hev.deriv_eq, hfull.deriv]
      ring

end

end GaloisForLFunctions.VorosClosedForm

namespace GaloisForLFunctions.VorosClosedForm

open Complex GaloisForLFunctions

noncomputable section

/-- The elementary factor `½ s(s−1)` of the completed `ξ`. -/
def elemFactor (s : ℂ) : ℂ := (1 / 2 : ℂ) * s * (s - 1)

/-- The completed `ξ`-function `ξ(s) = ½ s(s−1) Γ_ℝ(s) ζ(s)`. -/
def xiFun (s : ℂ) : ℂ := elemFactor s * (Complex.Gammaℝ s * riemannZeta s)

/-- The regularized logarithmic derivative of `ξ` at the origin: the `1/s` coming from the
elementary factor cancels the `−1/s` inside `½ψ(s/2)`, so this function is regular at `0`. -/
def xiLogDerivReg (s : ℂ) : ℂ :=
  1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (1 + s / 2) / 2
    + logDeriv riemannZeta s

/-- The Taylor coefficients of `ζ'/ζ` at the origin. -/
def zetaLogCoeff (j : ℕ) : ℂ := iteratedDeriv j (logDeriv riemannZeta) 0 / (j.factorial : ℂ)

/-- The Voros power sums, read off the generating function `−ξ'/ξ(s) = Σ_{k≥1} P_k s^{k−1}`. -/
def vorosPowerSum (k : ℕ) : ℂ :=
  -(iteratedDeriv (k - 1) xiLogDerivReg 0) / (((k - 1).factorial : ℕ) : ℂ)

/-! ## Smoothness at the origin -/

theorem analyticAt_riemannZeta_zero : AnalyticAt ℂ riemannZeta 0 := by
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hdiff.analyticOnNhd hopen 0 (by norm_num)

theorem contDiffAt_riemannZeta_zero : ContDiffAt ℂ (⊤ : ℕ∞) riemannZeta 0 :=
  analyticAt_riemannZeta_zero.contDiffAt

theorem riemannZeta_zero_ne_zero : riemannZeta 0 ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

theorem contDiffAt_logDeriv_riemannZeta_zero :
    ContDiffAt ℂ (⊤ : ℕ∞) (logDeriv riemannZeta) 0 := by
  have hz := analyticAt_riemannZeta_zero
  have hd : AnalyticAt ℂ (deriv riemannZeta) 0 := hz.deriv
  have hq : AnalyticAt ℂ (fun s : ℂ => deriv riemannZeta s / riemannZeta s) 0 :=
    hd.div hz riemannZeta_zero_ne_zero
  exact hq.contDiffAt

theorem contDiffAt_invSubOne_zero :
    ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => 1 / (z - 1)) 0 := by
  have hne : (0 : ℂ) - 1 ≠ 0 := by norm_num
  exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) hne

theorem contDiffAt_digammaHalfShift_zero :
    ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => Complex.digamma (1 + z / 2) / 2) 0 := by
  have haff : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => 1 + z / 2) 0 :=
    contDiffAt_const.add (contDiffAt_id.div_const 2)
  have hval : (1 : ℂ) + (0 : ℂ) / 2 = 1 := by norm_num
  have hdig : ContDiffAt ℂ (⊤ : ℕ∞) Complex.digamma ((fun z : ℂ => 1 + z / 2) 0) := by
    rw [show ((fun z : ℂ => 1 + z / 2) 0) = 1 from hval]
    exact contDiffAt_digamma_top (offPoles_of_re_pos (by norm_num))
  exact (hdig.comp 0 haff).div_const 2

end

end GaloisForLFunctions.VorosClosedForm

namespace GaloisForLFunctions.VorosClosedForm

open Complex GaloisForLFunctions

noncomputable section

theorem iteratedDeriv_const_eq_zero {c : ℂ} {m : ℕ} (hm : 1 ≤ m) :
    iteratedDeriv m (fun _ : ℂ => c) 0 = 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [iteratedDeriv_succ']
  simp

theorem iteratedDeriv_invSubOne_zero (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => 1 / (z - 1)) 0 = -(m.factorial : ℂ) := by
  rw [iteratedDeriv_inv_sub_one m 0 (by norm_num)]
  have hbase : ((0 : ℂ) - 1) ^ (m + 1) = (-1 : ℂ) ^ (m + 1) := by norm_num
  rw [hbase, pow_succ]
  have hne : ((-1 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem iteratedDeriv_digammaHalfShift_zero (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => Complex.digamma (1 + z / 2) / 2) 0
      = (1 / 2 : ℂ) ^ (m + 1) * iteratedDeriv m Complex.digamma 1 := by
  have hfun : (fun z : ℂ => Complex.digamma (1 + z / 2) / 2)
      = fun z : ℂ => (1 / 2 : ℂ) * Complex.digamma (1 + z / 2) := by
    funext z; ring
  have hcd : ContDiffAt ℂ ((m : ℕ) : WithTop ℕ∞)
      (fun z : ℂ => Complex.digamma (1 + z / 2)) 0 := by
    have haff : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => 1 + z / 2) 0 :=
      contDiffAt_const.add (contDiffAt_id.div_const 2)
    have hval : ((fun z : ℂ => 1 + z / 2) 0) = 1 := by norm_num
    have hdig : ContDiffAt ℂ (⊤ : ℕ∞) Complex.digamma ((fun z : ℂ => 1 + z / 2) 0) := by
      rw [hval]
      exact contDiffAt_digamma_top (offPoles_of_re_pos (by norm_num))
    exact (hdig.comp 0 haff).of_le (by exact_mod_cast le_top)
  rw [hfun, iteratedDeriv_const_mul _ hcd,
    iteratedDeriv_digamma_halfShift m 0 (by norm_num)]
  rw [show (1 : ℂ) + (0 : ℂ) / 2 = 1 by norm_num]
  ring

end

end GaloisForLFunctions.VorosClosedForm

namespace GaloisForLFunctions.VorosClosedForm

open Complex GaloisForLFunctions

noncomputable section

theorem xiLogDerivReg_split :
    xiLogDerivReg =
      ((fun z : ℂ => 1 / (z - 1)) + (fun _ : ℂ => -((Real.log Real.pi : ℂ) / 2)))
        + (fun z : ℂ => Complex.digamma (1 + z / 2) / 2) + logDeriv riemannZeta := by
  funext s
  simp only [Pi.add_apply, xiLogDerivReg]
  ring

theorem iteratedDeriv_xiLogDerivReg (m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv m xiLogDerivReg 0
      = -(m.factorial : ℂ)
        + (1 / 2 : ℂ) ^ (m + 1) * iteratedDeriv m Complex.digamma 1
        + (m.factorial : ℂ) * zetaLogCoeff m := by
  have h1 : ContDiffAt ℂ ((m : ℕ) : WithTop ℕ∞) (fun z : ℂ => 1 / (z - 1)) 0 :=
    contDiffAt_invSubOne_zero.of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℂ ((m : ℕ) : WithTop ℕ∞) (fun _ : ℂ => -((Real.log Real.pi : ℂ) / 2)) 0 :=
    contDiffAt_const
  have h3 : ContDiffAt ℂ ((m : ℕ) : WithTop ℕ∞)
      (fun z : ℂ => Complex.digamma (1 + z / 2) / 2) 0 :=
    contDiffAt_digammaHalfShift_zero.of_le (by exact_mod_cast le_top)
  have h4 : ContDiffAt ℂ ((m : ℕ) : WithTop ℕ∞) (logDeriv riemannZeta) 0 :=
    contDiffAt_logDeriv_riemannZeta_zero.of_le (by exact_mod_cast le_top)
  rw [xiLogDerivReg_split,
    iteratedDeriv_add (f := ((fun z : ℂ => 1 / (z - 1))
        + (fun _ : ℂ => -((Real.log Real.pi : ℂ) / 2)))
      + (fun z : ℂ => Complex.digamma (1 + z / 2) / 2))
      (g := logDeriv riemannZeta) ((h1.add h2).add h3) h4,
    iteratedDeriv_add (f := (fun z : ℂ => 1 / (z - 1))
        + (fun _ : ℂ => -((Real.log Real.pi : ℂ) / 2)))
      (g := fun z : ℂ => Complex.digamma (1 + z / 2) / 2) (h1.add h2) h3,
    iteratedDeriv_add (f := fun z : ℂ => 1 / (z - 1))
      (g := fun _ : ℂ => -((Real.log Real.pi : ℂ) / 2)) h1 h2,
    iteratedDeriv_invSubOne_zero, iteratedDeriv_const_eq_zero hm,
    iteratedDeriv_digammaHalfShift_zero]
  have hfacm : ((m.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hlast : iteratedDeriv m (logDeriv riemannZeta) 0 = (m.factorial : ℂ) * zetaLogCoeff m := by
    rw [zetaLogCoeff, mul_div_cancel₀ _ hfacm]
  rw [hlast]
  ring

/-- **The Voros closed form.**  For `k ≥ 2`,
`P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}` with `a_j = [s^j](ζ'/ζ)(s)`. -/
theorem vorosPowerSum_closed_form (k : ℕ) (hk : 2 ≤ k) :
    vorosPowerSum k
      = 1 - (-1 : ℂ) ^ k * riemannZeta ((k : ℕ) : ℂ) / 2 ^ k - zetaLogCoeff (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hfac : (((m + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  have hsub : (m + 2) - 1 = m + 1 := by omega
  rw [vorosPowerSum, hsub, iteratedDeriv_xiLogDerivReg (m + 1) (by omega),
    polygamma_one_eq_riemannZeta m,
    show ((1 : ℂ) / 2) ^ (m + 1 + 1) = 1 / 2 ^ (m + 1 + 1) by rw [div_pow, one_pow]]
  field_simp
  ring

end

end GaloisForLFunctions.VorosClosedForm

namespace GaloisForLFunctions.VorosClosedForm

open Complex GaloisForLFunctions

noncomputable section

theorem logDeriv_elemFactor {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv elemFactor s = 1 / s + 1 / (s - 1) := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hhalf : ((1 : ℂ) / 2) * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z) s :=
    differentiableAt_id.const_mul _
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const 1
  have hsplit : elemFactor = fun z : ℂ => ((1 / 2 : ℂ) * z) * (z - 1) := by
    funext z; rw [elemFactor]
  rw [hsplit, logDeriv_mul s hhalf hsub hd1 hd2]
  have h1 : logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z) s = 1 / s := by
    rw [logDeriv_apply, deriv_const_mul _ differentiableAt_id, deriv_id'']
    field_simp
  have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    simp
  rw [h1, h2]

theorem differentiableAt_GammaR {s : ℂ} (hpoles : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfun : Complex.Gammaℝ
      = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) :=
    funext Complex.Gammaℝ_def
  rw [hfun]
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    DifferentiableAt.const_cpow ((differentiableAt_id.neg).div_const 2) (Or.inl hpi0)
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hpoles).comp s (differentiableAt_id.div_const 2)
  exact hd1.mul hd2

theorem GammaR_ne_zero {s : ℂ} (hpoles : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    Complex.Gammaℝ s ≠ 0 := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero ?_ (Complex.Gamma_ne_zero hpoles)
  rcases eq_or_ne (-s / 2) 0 with h | h
  · rw [h]; simp
  · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero h).mpr hpi0

/-- **The regularized logarithmic derivative is the logarithmic derivative of `ξ`.**
The `1/s` of the elementary factor cancels the `−1/s` inside `½ψ(s/2)`. -/
theorem logDeriv_xiFun {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hpoles : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) (hz : riemannZeta s ≠ 0) :
    logDeriv xiFun s = xiLogDerivReg s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have helem : elemFactor s ≠ 0 := by
    rw [elemFactor]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs0) hsub
  have hG : Complex.Gammaℝ s ≠ 0 := GammaR_ne_zero hpoles
  have hdE : DifferentiableAt ℂ elemFactor s := by
    have : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s :=
      (differentiableAt_id.const_mul _).mul (differentiableAt_id.sub_const 1)
    exact this
  have hdG : DifferentiableAt ℂ Complex.Gammaℝ s := differentiableAt_GammaR hpoles
  have hdZ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hxi : xiFun = fun z : ℂ => elemFactor z * (Complex.Gammaℝ z * riemannZeta z) := rfl
  have hprodne : Complex.Gammaℝ s * riemannZeta s ≠ 0 := mul_ne_zero hG hz
  have step1 : logDeriv (fun z : ℂ => elemFactor z * (Complex.Gammaℝ z * riemannZeta z)) s
      = logDeriv elemFactor s
        + logDeriv (fun z : ℂ => Complex.Gammaℝ z * riemannZeta z) s :=
    logDeriv_mul s helem hprodne hdE (hdG.mul hdZ)
  have step2 : logDeriv (fun z : ℂ => Complex.Gammaℝ z * riemannZeta z) s
      = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s :=
    logDeriv_mul s hG hz hdG hdZ
  rw [hxi, step1, step2, logDeriv_elemFactor hs0 hs1,
    BohrGeneratorAxis.logDeriv_GammaR s hpoles]
  have hshift : Complex.digamma (s / 2 + 1) = Complex.digamma (s / 2) + (s / 2)⁻¹ :=
    Complex.digamma_apply_add_one (s / 2) hpoles
  have hdig : Complex.digamma (s / 2) / 2 = Complex.digamma (1 + s / 2) / 2 - 1 / s := by
    rw [show (1 : ℂ) + s / 2 = s / 2 + 1 by ring, hshift]
    field_simp
    ring
  rw [xiLogDerivReg]
  rw [show Complex.digamma (s / 2) / 2 = Complex.digamma (s / 2) / 2 from rfl]
  have hgoal : 1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2
      + logDeriv riemannZeta s)
      = 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (1 + s / 2) / 2
        + logDeriv riemannZeta s := by
    rw [hdig]
    ring
  exact hgoal

end

end GaloisForLFunctions.VorosClosedForm
