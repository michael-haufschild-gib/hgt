import GaloisForLFunctions.HTGeometry.IsingFieldGriffiths
import GaloisForLFunctions.RHTower.XiMagnetizationGHSConcavity
import GaloisForLFunctions.RHTower.XiCosineShiftNonrealZeroCount
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.HTGeometry.ArchimedeanSzegoCounterterm
import GaloisForLFunctions.HTGeometry.TanhSelfBound

/-!
# Free magnetization dominance and the harmonic Griffiths–Simon program

A Griffiths–Simon producer of `Ξ` is a sequence of zero-field ferromagnetic Ising magnetizations
`X_n = Σ_k c_{n,k} σ_k` (`J ≥ 0`, masses `c ≥ 0`) whose centred characteristic functions
`E[e^{izX_n}]` converge locally uniformly on `ℂ` to `Ξ(z)/Ξ(0)`. By the Lee–Yang theorem such a
producer would prove RH.

* `tendsto_isingMag_xiRealLogDeriv`: along a producer, the magnetization `⟨X_n⟩_w` in every real
  field `w` converges to the Riemann magnetization `(ξ'/ξ)(½ + w)`. The magnetization is
  `−iφ'(−iw)/φ(−iw)`, and derivatives pass to the limit.
* `eventually_freeMag_le_xiRealLogDeriv`, the **free magnetization dominance law**: for every
  `w ≥ 0`, eventually `Σ_k c_{n,k} tanh(c_{n,k} w) ≤ (ξ'/ξ)(½ + w) + ε`. This is Griffiths'
  inequality `⟨σ_k⟩ ≥ tanh h_k` (`HTGeometry/IsingFieldGriffiths`) passed to the limit.
* `xiRealLogDeriv_le`: the Gamma cap
  `(ξ'/ξ)(½ + w) ≤ 1/(½+w) + 1/(w−½) − (log π)/2 + (log((½+w)/2))/2` for `w > ½`. It uses
  `Re ψ ≤ log` and `ζ'/ζ ≤ 0` on the real axis.
* `harmSum_ge`, `harm_minus_gamma_gt`: at `w = 2000`, the free harmonic magnetization
  `Σ_{k=7}^{N} tanh(1000/k)/(2k)` exceeds the cap by more than `1/200` for `N ≥ 10⁶`. The proof
  combines an exact head `Σ_{k=7}^{30} 1/(2k)`, an integral comparison for the antitone tail, the
  bounds `tanh y ≥ 1 − 2e^{−2y}` and `tanh y ≥ y − y³/3`, and certified values of `log π`,
  `log 31` and `e`.
* `not_tendstoLocallyUniformly_harmonic_isingChar`: **no producer contains the harmonic masses
  `1/(2k)`, `K ≤ k ≤ N_n`, from `K ≤ 7`**, whatever the graph and couplings.

At large field the asymptotic gap is `½H_{K−1} − γ − log 2`. It is positive exactly when
`H_{K−1} ≥ 2γ + log 4`, the same threshold at which the free harmonic zero count matches the
second coefficient of the Riemann–von Mangoldt formula.
-/

open Complex Filter Topology Finset
open GaloisForLFunctions.HTGeometry.LeeYang

namespace RHTower.GriffithsSimon

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted magnetization `X = Σ_k c_k σ_k`. -/
def magX (c : V → ℝ) (D : Finset V) : ℝ := ∑ k, c k * spin D k

/-- The centred characteristic function `E[e^{izX}]` of the zero-field Ising magnetization. -/
def isingChar (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (z : ℂ) : ℂ :=
  (∑ D : Finset V, (isingWeight J E D : ℂ) * Complex.exp (I * z * (magX c D : ℂ))) /
    (Zpart J E : ℂ)

/-- The magnetization `⟨X⟩_w` in the field `w` (tilt `e^{wX}`). -/
def isingMag (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (w : ℝ) : ℝ :=
  (∑ D : Finset V, isingWeight J E D * Real.exp (w * magX c D) * magX c D) /
    ∑ D : Finset V, isingWeight J E D * Real.exp (w * magX c D)

theorem fieldFactor_eq_exp_magX (c : V → ℝ) (w : ℝ) (D : Finset V) :
    fieldFactor (fun k => c k * w) D = Real.exp (w * magX c D) := by
  rw [fieldFactor, magX, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem tilt_sum_pos (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (w : ℝ) :
    0 < ∑ D : Finset V, isingWeight J E D * Real.exp (w * magX c D) :=
  Finset.sum_pos (fun D _ => mul_pos (isingWeight_pos J E D) (Real.exp_pos _))
    ⟨∅, Finset.mem_univ _⟩

/-- **Free magnetization dominance**, normalized form. -/
theorem freeMag_le_isingMag (J : V → V → ℝ) (E : Finset (V × V)) (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2)
    (c : V → ℝ) (hc : ∀ k, 0 ≤ c k) {w : ℝ} (hw : 0 ≤ w) :
    ∑ k, c k * Real.tanh (c k * w) ≤ isingMag J E c w := by
  have h := freeMagnetization_le J E hJ c hc hw
  simp only [fieldFactor_eq_exp_magX] at h
  rw [isingMag, le_div_iff₀ (tilt_sum_pos J E c w)]
  have e : ∑ D : Finset V, isingWeight J E D * Real.exp (w * magX c D) * ∑ k, c k * spin D k =
      ∑ D : Finset V, isingWeight J E D * Real.exp (w * magX c D) * magX c D := rfl
  linarith

theorem hasDerivAt_isingChar (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (z : ℂ) :
    HasDerivAt (isingChar J E c)
      ((∑ D : Finset V, (isingWeight J E D : ℂ) * (I * (magX c D : ℂ) *
        Complex.exp (I * z * (magX c D : ℂ)))) / (Zpart J E : ℂ)) z := by
  unfold isingChar
  refine HasDerivAt.div_const ?_ _
  refine HasDerivAt.fun_sum fun D _ => ?_
  have h : HasDerivAt (fun y : ℂ => Complex.exp (I * y * (magX c D : ℂ)))
      (Complex.exp (I * z * (magX c D : ℂ)) * (I * 1 * (magX c D : ℂ))) z :=
    (((hasDerivAt_id z).const_mul I).mul_const (magX c D : ℂ)).cexp
  refine (h.const_mul (isingWeight J E D : ℂ)).congr_deriv ?_
  ring

theorem exp_I_neg_I_mul (w x : ℝ) :
    Complex.exp (I * -(I * (w : ℂ)) * (x : ℂ)) = ((Real.exp (w * x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(w : ℂ) * (x : ℂ)) * Complex.I_mul_I

theorem isingChar_neg_I_mul (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (w : ℝ) :
    isingChar J E c (-(I * w)) =
      (((∑ D : Finset V, isingWeight J E D * Real.exp (w * magX c D)) / Zpart J E : ℝ) : ℂ) := by
  unfold isingChar
  simp_rw [exp_I_neg_I_mul]
  push_cast
  rfl

theorem deriv_isingChar_neg_I_mul (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (w : ℝ) :
    deriv (isingChar J E c) (-(I * w)) =
      I * (((∑ D : Finset V, isingWeight J E D * Real.exp (w * magX c D) * magX c D) /
        Zpart J E : ℝ) : ℂ) := by
  rw [(hasDerivAt_isingChar J E c _).deriv]
  simp_rw [exp_I_neg_I_mul]
  push_cast
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun D _ => ?_
  ring

theorem ofReal_div_eq_neg_I_mul (A B Z : ℝ) (hB : B ≠ 0) (hZ : Z ≠ 0) :
    ((A / B : ℝ) : ℂ) = -I * (I * ((A / Z : ℝ) : ℂ)) / ((B / Z : ℝ) : ℂ) := by
  have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ
  push_cast
  rw [← mul_assoc, neg_mul, Complex.I_mul_I]
  field_simp

/-- The magnetization is read off the characteristic function at `z = −iw`. -/
theorem isingMag_eq (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (w : ℝ) :
    ((isingMag J E c w : ℝ) : ℂ) =
      -I * deriv (isingChar J E c) (-(I * w)) / isingChar J E c (-(I * w)) := by
  rw [deriv_isingChar_neg_I_mul, isingChar_neg_I_mul, isingMag]
  exact ofReal_div_eq_neg_I_mul _ _ _ (tilt_sum_pos J E c w).ne' (Zpart_pos J E).ne'

/-- **Magnetizations of a producer converge to the Riemann magnetization.** If the centred
characteristic functions of Ising magnetizations converge locally uniformly on `ℂ` to
`Ξ(z)/Ξ(0)`, then for every real field `w` the magnetizations converge to `(ξ'/ξ)(½ + w)`. -/
theorem tendsto_isingMag_xiRealLogDeriv {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (c : ∀ n, ι n → ℝ)
    (hconv : TendstoLocallyUniformly (fun n => isingChar (J n) (E n) (c n))
      (fun z => XiC z / XiC 0) atTop) (w : ℝ) :
    Tendsto (fun n => isingMag (J n) (E n) (c n) w) atTop (𝓝 (xiRealLogDeriv w)) := by
  set z₀ : ℂ := -(I * w) with hz₀
  have hXiCd : Differentiable ℂ XiC := fun z => (hasDerivAt_XiC z).differentiableAt
  have hlimd : Differentiable ℂ (fun z => XiC z / XiC 0) := hXiCd.div_const _
  have hval : Tendsto (fun n => isingChar (J n) (E n) (c n) z₀) atTop (𝓝 (XiC z₀ / XiC 0)) :=
    hconv.tendsto_comp hlimd.continuous.continuousAt tendsto_const_nhds
  have hder : Tendsto (fun n => deriv (isingChar (J n) (E n) (c n)) z₀) atTop
      (𝓝 (deriv (fun z => XiC z / XiC 0) z₀)) := by
    have h := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform (j := 1)
      isOpen_univ (tendstoLocallyUniformlyOn_univ.mpr hconv)
      (Filter.Eventually.of_forall fun n => fun z _ =>
        (hasDerivAt_isingChar (J n) (E n) (c n) z).differentiableAt.differentiableWithinAt)
      (Set.mem_univ z₀)
    simpa only [iteratedDeriv_one] using h
  have hpt : (1 : ℂ) / 2 + z₀ * I = 1 / 2 + (w : ℂ) := by
    rw [hz₀]; linear_combination (-(w : ℂ)) * Complex.I_mul_I
  have hXiCz : XiC z₀ = xi (1 / 2 + (w : ℂ)) := by rw [XiC, hpt]
  have hdlim : deriv (fun z => XiC z / XiC 0) z₀ = deriv xi (1 / 2 + (w : ℂ)) * I / XiC 0 := by
    have := ((hasDerivAt_XiC z₀).div_const (XiC 0)).deriv
    rw [this, hpt]
  have hxi0 : xi (1 / 2 + (w : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero w
  have hXi0 : XiC 0 ≠ 0 := XiC_zero_ne
  have hlimne : XiC z₀ / XiC 0 ≠ 0 := by rw [hXiCz]; exact div_ne_zero hxi0 hXi0
  have hratio := (hder.const_mul (-I)).div hval hlimne
  have hlimval : -I * deriv (fun z => XiC z / XiC 0) z₀ / (XiC z₀ / XiC 0) =
      logDeriv xi (1 / 2 + (w : ℂ)) := by
    rw [hdlim, hXiCz, logDeriv_apply]
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hlimval] at hratio
  have hC : Tendsto (fun n => ((isingMag (J n) (E n) (c n) w : ℝ) : ℂ)) atTop
      (𝓝 (logDeriv xi (1 / 2 + (w : ℂ)))) :=
    hratio.congr fun n => (isingMag_eq (J n) (E n) (c n) w).symm
  have hre := (Complex.continuous_re.tendsto _).comp hC
  exact hre.congr fun n => Complex.ofReal_re _

/-- **Free magnetization dominance for producers of `Ξ`.** For ferromagnetic Ising magnetizations
`X_n = Σ_k c_{n,k} σ_k` (`J ≥ 0`, `c ≥ 0`) whose centred characteristic functions converge locally
uniformly to `Ξ(z)/Ξ(0)`, every field `w ≥ 0` and every `ε > 0`, eventually
`Σ_k c_{n,k} tanh(c_{n,k} w) ≤ (ξ'/ξ)(½ + w) + ε`. -/
theorem eventually_freeMag_le_xiRealLogDeriv {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hconv : TendstoLocallyUniformly (fun n => isingChar (J n) (E n) (c n))
      (fun z => XiC z / XiC 0) atTop) {w : ℝ} (hw : 0 ≤ w) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∑ k, c n k * Real.tanh (c n k * w) ≤ xiRealLogDeriv w + ε := by
  have h := tendsto_isingMag_xiRealLogDeriv J E c hconv w
  filter_upwards [(h.eventually (gt_mem_nhds (by linarith : xiRealLogDeriv w < xiRealLogDeriv w + ε)))]
    with n hn
  exact (freeMag_le_isingMag (J n) (E n) (hJ n) (c n) (hc n) hw).trans hn.le

/-! ## An upper bound for the Riemann magnetization -/

theorem xiRealLogDeriv_eq_fourFactor {w : ℝ} (hw : 1 / 2 < w) :
    xiRealLogDeriv w = 1 / (1 / 2 + w) + 1 / ((1 / 2 + w) - 1) - Real.log Real.pi / 2 +
      (Complex.digamma ((((1 / 2 + w) / 2 : ℝ)) : ℂ)).re / 2 +
      (logDeriv riemannZeta (((1 / 2 + w : ℝ)) : ℂ)).re := by
  set x : ℝ := 1 / 2 + w with hx
  have hx1 : 1 < x := by rw [hx]; linarith
  have hs : (1 / 2 + (w : ℂ)) = ((x : ℝ) : ℂ) := by rw [hx]; push_cast; ring
  have hsre : 1 < ((x : ℝ) : ℂ).re := by simpa using hx1
  rw [xiRealLogDeriv, hs, logDeriv_xi_fourFactor hsre]
  have h1 : (1 / ((x : ℝ) : ℂ)).re = 1 / x := by
    rw [show (1 / ((x : ℝ) : ℂ)) = ((1 / x : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have h2 : (1 / (((x : ℝ) : ℂ) - 1)).re = 1 / (x - 1) := by
    rw [show (1 / (((x : ℝ) : ℂ) - 1)) = ((1 / (x - 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have h3 : ((Real.log Real.pi : ℂ) / 2).re = Real.log Real.pi / 2 := by
    rw [show ((Real.log Real.pi : ℂ) / 2) = ((Real.log Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hhalf : ((x : ℝ) : ℂ) / 2 = (((x / 2 : ℝ)) : ℂ) := by push_cast; ring
  have h4 : (Complex.digamma (((x : ℝ) : ℂ) / 2) / 2).re =
      (Complex.digamma (((x / 2 : ℝ)) : ℂ)).re / 2 := by
    rw [hhalf, Complex.div_re]
    simp only [Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_div]
    ring
  rw [Complex.add_re, Complex.add_re, Complex.sub_re, Complex.add_re, h1, h2, h3, h4]

theorem re_logDeriv_riemannZeta_nonpos {x : ℝ} (hx : 1 < x) :
    (logDeriv riemannZeta (x : ℂ)).re ≤ 0 := by
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  rw [logDeriv_apply, show deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ) =
    -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x : ℂ) by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hx']; ring,
    Complex.neg_re, LSeries, Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt hx'),
    neg_nonpos]
  refine tsum_nonneg fun n => ?_
  rw [re_term_vonMangoldt]
  unfold vonMangoldtTermR
  split_ifs
  · exact le_rfl
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le

/-- **The Riemann magnetization is at most its Gamma part.** For `w > ½`,
`(ξ'/ξ)(½ + w) ≤ 1/(½+w) + 1/(w−½) − (log π)/2 + (log((½+w)/2))/2`. -/
theorem xiRealLogDeriv_le {w : ℝ} (hw : 1 / 2 < w) :
    xiRealLogDeriv w ≤ 1 / (1 / 2 + w) + 1 / (w - 1 / 2) - Real.log Real.pi / 2 +
      Real.log ((1 / 2 + w) / 2) / 2 := by
  rw [xiRealLogDeriv_eq_fourFactor hw]
  have hpsi := re_digamma_le_log (y := (1 / 2 + w) / 2) (by linarith)
  have hz := re_logDeriv_riemannZeta_nonpos (x := 1 / 2 + w) (by linarith)
  have e : 1 / (1 / 2 + w) + 1 / ((1 / 2 + w) - 1) = 1 / (1 / 2 + w) + 1 / (w - 1 / 2) := by ring_nf
  rw [e]
  linarith

end

end RHTower.GriffithsSimon



namespace RHTower.GriffithsSimon

/-- `tanh y ≥ 1 − 2e^{−2y}` for every real `y`. -/
theorem one_sub_two_exp_le_tanh (y : ℝ) : 1 - 2 * Real.exp (-2 * y) ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  set a := Real.exp y with ha
  set b := Real.exp (-y) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hab : a * b = 1 := by rw [ha, hb, ← Real.exp_add]; simp
  have hb2 : Real.exp (-2 * y) = b ^ 2 := by rw [hb, ← Real.exp_nat_mul]; ring_nf
  rw [hb2]
  rw [show (a - b) / 2 / ((a + b) / 2) = (a - b) / (a + b) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg b, mul_pos hb0 hb0, mul_pos (mul_pos hb0 hb0) hb0]

/-- `tanh y ≥ y − y³/3` for `y ≥ 0`. -/
theorem sub_cube_le_tanh {y : ℝ} (hy : 0 ≤ y) : y - y ^ 3 / 3 ≤ Real.tanh y := by
  have hmono : MonotoneOn (fun t : ℝ => Real.tanh t - t + t ^ 3 / 3) (Set.Ici 0) := by
    have hd : ∀ t, HasDerivAt (fun t : ℝ => Real.tanh t - t + t ^ 3 / 3)
        (1 / Real.cosh t ^ 2 - 1 + t ^ 2) t := by
      intro t
      have := ((_root_.HTGeometry.hasDerivAt_tanh t).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 3 t).div_const 3)
      exact this.congr_deriv (by simp)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv]
      have ht0 : 0 ≤ t := le_of_lt ht
      have h1 : Real.tanh t ≤ t := GaloisForLFunctions.HTGeometry.tanh_le_self ht0
      have h2 : 0 ≤ Real.tanh t := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr ht0) (Real.cosh_pos t).le
      have hsech : 1 / Real.cosh t ^ 2 = 1 - Real.tanh t ^ 2 := by
        rw [Real.tanh_eq_sinh_div_cosh, div_pow]
        have hc : Real.cosh t ^ 2 ≠ 0 := pow_ne_zero 2 (Real.cosh_pos t).ne'
        field_simp
        nlinarith [Real.cosh_sq_sub_sinh_sq t]
      rw [hsech]
      nlinarith
  have h := hmono (Set.self_mem_Ici) hy hy
  simp at h
  linarith

end RHTower.GriffithsSimon

namespace RHTower.GriffithsSimon

open intervalIntegral

/-- The harmonic tilted term `tanh(1000/x)/(2x)` (field `w = 2000`, mass `1/(2x)`). -/
noncomputable def harmTerm (x : ℝ) : ℝ := Real.tanh (1000 / x) / (2 * x)

theorem tanh_monotone : Monotone Real.tanh := by
  refine monotone_of_deriv_nonneg (fun x => (_root_.HTGeometry.hasDerivAt_tanh x).differentiableAt) ?_
  intro x
  rw [(_root_.HTGeometry.hasDerivAt_tanh x).deriv]
  positivity

theorem tanh_nonneg_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le

theorem harmTerm_antitoneOn : AntitoneOn harmTerm (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  unfold harmTerm
  have h1 : Real.tanh (1000 / y) ≤ Real.tanh (1000 / x) :=
    tanh_monotone (div_le_div_of_nonneg_left (by norm_num) hx hxy)
  have h0 : 0 ≤ Real.tanh (1000 / y) := tanh_nonneg_of_nonneg (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [tanh_nonneg_of_nonneg (show (0 : ℝ) ≤ 1000 / x by positivity)]

theorem continuousOn_harmTerm : ContinuousOn harmTerm (Set.Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := (Set.mem_Ioi.mp hx).ne'
  unfold harmTerm
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div ?_ (continuousAt_const.mul continuousAt_id) (by simpa using hx0)
  exact (_root_.HTGeometry.hasDerivAt_tanh _).continuousAt.comp
    (continuousAt_const.div continuousAt_id hx0)

theorem intervalIntegrable_harmTerm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable harmTerm MeasureTheory.volume a b := by
  refine (continuousOn_harmTerm.mono ?_).intervalIntegrable
  intro x hx
  rw [Set.uIcc] at hx
  simp only [Set.mem_Ioi]
  exact lt_of_lt_of_le (lt_min ha hb) hx.1

/-- The exact antiderivative identity `∫_a^b (2000/x²) e^{−2000/x} = e^{−2000/b} − e^{−2000/a}`. -/
theorem integral_exp_neg_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, 2000 / x ^ 2 * Real.exp (-(2000 / x)) =
      Real.exp (-(2000 / b)) - Real.exp (-(2000 / a)) := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hab] at hx; linarith [hx.1]
  refine integral_eq_sub_of_hasDerivAt (f := fun x => Real.exp (-(2000 / x))) (fun x hx => ?_) ?_
  · have hx0 : x ≠ 0 := (hpos x hx).ne'
    have h := (((hasDerivAt_const x (2000 : ℝ)).div (hasDerivAt_id x) hx0).neg).exp
    refine h.congr_deriv ?_
    simp only [id, Pi.neg_apply, Pi.div_apply, zero_mul, zero_sub, mul_one, neg_div, neg_neg]
    ring
  · refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    exact ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).mul
      (continuousAt_const.div continuousAt_id hx0).neg.rexp).continuousWithinAt

theorem harmTerm_ge_exp {x : ℝ} (hx : 0 < x) :
    1 / (2 * x) - x / 2000 * (2000 / x ^ 2 * Real.exp (-(2000 / x))) ≤ harmTerm x := by
  unfold harmTerm
  have h := one_sub_two_exp_le_tanh (1000 / x)
  have he : Real.exp (-2 * (1000 / x)) = Real.exp (-(2000 / x)) := by congr 1; ring
  rw [he] at h
  have hx2 : 0 < 2 * x := by linarith
  rw [le_div_iff₀ hx2]
  have : (1 / (2 * x) - x / 2000 * (2000 / x ^ 2 * Real.exp (-(2000 / x)))) * (2 * x) =
      1 - 2 * Real.exp (-(2000 / x)) := by field_simp
  rw [this]; exact h

theorem harmTerm_ge_poly {x : ℝ} (hx : 1000 ≤ x) :
    500 / x ^ 2 - 1000 ^ 3 / (6 * x ^ 4) ≤ harmTerm x := by
  unfold harmTerm
  have hx0 : 0 < x := by linarith
  have h := sub_cube_le_tanh (show (0 : ℝ) ≤ 1000 / x by positivity)
  have hx2 : 0 < 2 * x := by linarith
  rw [le_div_iff₀ hx2]
  have : (500 / x ^ 2 - 1000 ^ 3 / (6 * x ^ 4)) * (2 * x) = 1000 / x - (1000 / x) ^ 3 / 3 := by
    field_simp; ring
  rw [this]; exact h

theorem integral_inv_half {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, 1 / (2 * x) = (Real.log b - Real.log a) / 2 := by
  have hb : 0 < b := by linarith
  have h : ∫ x in a..b, 1 / (2 * x) = (1 / 2) * ∫ x in a..b, x⁻¹ := by
    rw [← integral_const_mul]; congr 1; funext x; field_simp
  rw [h, integral_inv_of_pos ha hb, Real.log_div hb.ne' ha.ne']
  ring

theorem intervalIntegrable_expPart {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    IntervalIntegrable (fun x => 1 / (2 * x) - c * (2000 / x ^ 2 * Real.exp (-(2000 / x))))
      MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ?_
  rw [Set.uIcc_of_le hab] at hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  refine ContinuousAt.continuousWithinAt ?_
  refine (continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by simpa using hx0)).sub
    (continuousAt_const.mul ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).mul
      (continuousAt_const.div continuousAt_id hx0).neg.rexp))

/-- The integral of the harmonic term over one block, with exponential loss weight `c`. -/
theorem integral_harmTerm_ge_block {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcx : ∀ x ∈ Set.Icc a b, x / 2000 ≤ c) :
    (Real.log b - Real.log a) / 2 - c * (Real.exp (-(2000 / b)) - Real.exp (-(2000 / a))) ≤
      ∫ x in a..b, harmTerm x := by
  have hb : 0 < b := by linarith
  have hle : ∀ x ∈ Set.Icc a b, 1 / (2 * x) - c * (2000 / x ^ 2 * Real.exp (-(2000 / x))) ≤ harmTerm x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    refine le_trans ?_ (harmTerm_ge_exp hx0)
    have hg : 0 ≤ 2000 / x ^ 2 * Real.exp (-(2000 / x)) := by positivity
    have := mul_le_mul_of_nonneg_right (hcx x hx) hg
    linarith
  have hint := integral_mono_on hab (intervalIntegrable_expPart ha hab c)
    (intervalIntegrable_harmTerm ha hb) hle
  have hsplit : ∫ x in a..b, (1 / (2 * x) - c * (2000 / x ^ 2 * Real.exp (-(2000 / x)))) =
      (Real.log b - Real.log a) / 2 - c * (Real.exp (-(2000 / b)) - Real.exp (-(2000 / a))) := by
    have hpos : ∀ x ∈ Set.uIcc a b, x ≠ 0 := fun x hx => by
      rw [Set.uIcc_of_le hab] at hx; linarith [hx.1]
    rw [integral_sub, integral_const_mul, integral_inv_half ha hab, integral_exp_neg_div ha hab]
    · exact ContinuousOn.intervalIntegrable fun x hx =>
        (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
          (mul_ne_zero two_ne_zero (hpos x hx))).continuousWithinAt
    · exact ContinuousOn.intervalIntegrable fun x hx =>
        (continuousAt_const.mul ((continuousAt_const.div (continuousAt_id.pow 2)
          (pow_ne_zero 2 (hpos x hx))).mul
          (continuousAt_const.div continuousAt_id (hpos x hx)).neg.rexp)).continuousWithinAt
  linarith

/-- `∫_{31}^{1000} tanh(1000/x)/(2x) dx ≥ (log 1000 − log 31)/2 − (e^{−2} − e^{−3})/2 − e^{−3}/3`. -/
theorem integral_harmTerm_middle :
    (Real.log 1000 - Real.log 31) / 2 - ((Real.exp (-2) - Real.exp (-3)) / 2 + Real.exp (-3) / 3) ≤
      ∫ x in (31 : ℝ)..1000, harmTerm x := by
  have h1 := integral_harmTerm_ge_block (a := 31) (b := 2000 / 3) (c := 1 / 3) (by norm_num)
    (by norm_num) (fun x hx => by rw [div_le_iff₀ (by norm_num)]; linarith [hx.2])
  have h2 := integral_harmTerm_ge_block (a := 2000 / 3) (b := 1000) (c := 1 / 2) (by norm_num)
    (by norm_num) (fun x hx => by rw [div_le_iff₀ (by norm_num)]; linarith [hx.2])
  rw [← integral_add_adjacent_intervals (b := 2000 / 3) (intervalIntegrable_harmTerm (by norm_num)
    (by norm_num)) (intervalIntegrable_harmTerm (by norm_num) (by norm_num))]
  have e1 : Real.exp (-(2000 / (2000 / 3 : ℝ))) = Real.exp (-3) := by norm_num
  have e2 : Real.exp (-(2000 / (1000 : ℝ))) = Real.exp (-2) := by norm_num
  rw [e1] at h1 h2
  rw [e2] at h2
  have hpos : 0 ≤ Real.exp (-(2000 / (31 : ℝ))) := (Real.exp_pos _).le
  linarith

/-- `∫_{1000}^{M} tanh(1000/x)/(2x) dx ≥ 4/9 − 500/M` for `M ≥ 1000`. -/
theorem integral_harmTerm_tail {M : ℝ} (hM : 1000 ≤ M) :
    4 / 9 - 500 / M ≤ ∫ x in (1000 : ℝ)..M, harmTerm x := by
  have hM0 : 0 < M := by linarith
  have hpoly : ∫ x in (1000 : ℝ)..M, (500 / x ^ 2 - 1000 ^ 3 / (6 * x ^ 4)) =
      (-500 / M + 1000 ^ 3 / (18 * M ^ 3)) - (-500 / 1000 + 1000 ^ 3 / (18 * 1000 ^ 3)) := by
    refine integral_eq_sub_of_hasDerivAt (f := fun x => -500 / x + 1000 ^ 3 / (18 * x ^ 3))
      (fun x hx => ?_) ?_
    · rw [Set.uIcc_of_le hM] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have h := ((hasDerivAt_const x (-500 : ℝ)).div (hasDerivAt_id x) hx0).add
        ((hasDerivAt_const x ((1000 : ℝ) ^ 3)).div ((hasDerivAt_pow 3 x).const_mul 18)
          (mul_ne_zero (by norm_num) (pow_ne_zero 3 hx0)))
      refine h.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    · refine ContinuousOn.intervalIntegrable fun x hx => ?_
      rw [Set.uIcc_of_le hM] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      exact ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).sub
        (continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 4))
          (mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)))).continuousWithinAt
  have hint := integral_mono_on hM (by
      refine ContinuousOn.intervalIntegrable fun x hx => ?_
      rw [Set.uIcc_of_le hM] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      exact ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).sub
        (continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 4))
          (mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)))).continuousWithinAt)
    (intervalIntegrable_harmTerm (by norm_num) hM0) (fun x hx => harmTerm_ge_poly hx.1)
  rw [hpoly] at hint
  have h3 : 0 ≤ (1000 : ℝ) ^ 3 / (18 * M ^ 3) := by positivity
  have : (-500 / M + 1000 ^ 3 / (18 * M ^ 3)) - (-500 / 1000 + 1000 ^ 3 / (18 * 1000 ^ 3)) =
      4 / 9 - 500 / M + 1000 ^ 3 / (18 * M ^ 3) := by ring
  linarith

/-- The free harmonic sum over `[31, N]` dominates the integral from `31` to `N + 1`. -/
theorem integral_le_sum_harmTerm (N : ℕ) (hN : 31 ≤ N) :
    ∫ x in (31 : ℝ)..(N + 1 : ℕ), harmTerm x ≤ ∑ k ∈ Finset.Icc 31 N, harmTerm k := by
  have hcast : ((N + 1 : ℕ) : ℝ) = 31 + ((N - 30 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast]
  refine (AntitoneOn.integral_le_sum (harmTerm_antitoneOn.mono fun x hx => ?_)).trans_eq ?_
  · simp only [Set.mem_Icc] at hx; simp only [Set.mem_Ioi]; linarith [hx.1]
  · rw [Finset.sum_bij' (fun i _ => i + 31) (fun k _ => k - 31)]
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · intro i _; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · intro i _; push_cast; ring_nf

/-- Exponentials are tiny on the head `7 ≤ k ≤ 30`. -/
theorem harmTerm_head_ge (k : ℕ) (hk : k ∈ Finset.Icc 7 30) :
    1 / (2 * (k : ℝ)) - Real.exp (-66) / 7 ≤ harmTerm k := by
  simp only [Finset.mem_Icc] at hk
  have hk7 : (7 : ℝ) ≤ k := by exact_mod_cast hk.1
  have hk30 : (k : ℝ) ≤ 30 := by exact_mod_cast hk.2
  have hk0 : (0 : ℝ) < k := by linarith
  refine le_trans ?_ (harmTerm_ge_exp hk0)
  have hexp : Real.exp (-(2000 / (k : ℝ))) ≤ Real.exp (-66) := by
    rw [Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ hk0]; linarith
  have e : (k : ℝ) / 2000 * (2000 / (k : ℝ) ^ 2 * Real.exp (-(2000 / (k : ℝ)))) =
      Real.exp (-(2000 / (k : ℝ))) / k := by field_simp
  rw [e]
  have h1 : Real.exp (-(2000 / (k : ℝ))) / k ≤ Real.exp (-66) / k :=
    div_le_div_of_nonneg_right hexp hk0.le
  have h2 : Real.exp (-66) / k ≤ Real.exp (-66) / 7 :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hk7
  linarith

/-- **Lower bound for the free harmonic magnetization at field `2000`.** For `N ≥ 1000`,
`Σ_{k=7}^{N} tanh(1000/k)/(2k)` is at least
`(H₃₀ − H₆)/2 − 24e^{−66}/7 + (log 1000 − log 31)/2 − (e^{−2} − e^{−3})/2 − e^{−3}/3 + 4/9 − 500/(N+1)`. -/
theorem harmSum_ge (N : ℕ) (hN : 1000 ≤ N) :
    (∑ k ∈ Finset.Icc (7 : ℕ) 30, 1 / (2 * (k : ℝ))) - 24 * Real.exp (-66) / 7 +
        ((Real.log 1000 - Real.log 31) / 2 -
          ((Real.exp (-2) - Real.exp (-3)) / 2 + Real.exp (-3) / 3)) +
        (4 / 9 - 500 / ((N + 1 : ℕ) : ℝ)) ≤
      ∑ k ∈ Finset.Icc 7 N, harmTerm k := by
  have hsplit : Finset.Icc 7 N = Finset.Icc 7 30 ∪ Finset.Icc 31 N := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 7 30) (Finset.Icc 31 N) := by
    rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hhead : (∑ k ∈ Finset.Icc (7 : ℕ) 30, 1 / (2 * (k : ℝ))) - 24 * Real.exp (-66) / 7 ≤
      ∑ k ∈ Finset.Icc (7 : ℕ) 30, harmTerm (k : ℝ) := by
    have h := Finset.sum_le_sum harmTerm_head_ge
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h
    have h24 : ((30 + 1 - 7 : ℕ) : ℝ) = 24 := by norm_num
    rw [h24] at h
    linarith
  have hM : (1000 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 1000 ≤ N + 1)
  have htail := integral_le_sum_harmTerm N (by omega)
  rw [← integral_add_adjacent_intervals (b := 1000)
    (intervalIntegrable_harmTerm (by norm_num) (by norm_num))
    (intervalIntegrable_harmTerm (by norm_num) (by linarith))] at htail
  have hmid := integral_harmTerm_middle
  have hend := integral_harmTerm_tail hM
  linarith

/-! ## Numerical constants -/

theorem log_thirtyOne_le : Real.log 31 ≤ 5 * 0.6931471808 - 1 / 32 := by
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have hq : 1 - (32 / 31 : ℝ)⁻¹ ≤ Real.log (32 / 31) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hdiv : Real.log (32 / 31) = Real.log 32 - Real.log 31 := Real.log_div (by norm_num) (by norm_num)
  have := Real.log_two_lt_d9
  norm_num at hq
  linarith

theorem log_pi_ge : 1.1447216 ≤ Real.log Real.pi := by
  have hu1 : |(570796 / 2570796 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hu1
  have hpart : ∑ k ∈ Finset.range 3, 2 * (1 / (2 * (k : ℝ) + 1)) *
      (570796 / 2570796 : ℝ) ^ (2 * k + 1) ≤
      Real.log (1 + 570796 / 2570796) - Real.log (1 - 570796 / 2570796) :=
    sum_le_hasSum _ (fun k _ => by positivity) hs
  have hlog : Real.log (1 + 570796 / 2570796) - Real.log (1 - 570796 / 2570796) =
      Real.log (3.141592 / 2) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1; norm_num
  rw [hlog] at hpart
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hpart
  norm_num at hpart
  have hpi : Real.log (3.141592) ≤ Real.log Real.pi :=
    Real.log_le_log (by norm_num) Real.pi_gt_d6.le
  have hsplit : Real.log (3.141592) = Real.log 2 + Real.log (3.141592 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_gt_d9
  norm_num at hsplit hpi hpart
  linarith

theorem exp_neg_two_le : Real.exp (-2) ≤ 1 / 2.7182818283 ^ 2 := by
  rw [Real.exp_neg, show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num, one_div]
  exact inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2)

theorem exp_neg_three_ge : 1 / 2.7182818286 ^ 3 ≤ Real.exp (-3) := by
  rw [Real.exp_neg, show Real.exp 3 = Real.exp 1 ^ 3 by rw [← Real.exp_nat_mul]; norm_num, one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3)

theorem exp_neg_sixtySix_le : Real.exp (-66) ≤ 1 / 2 ^ 66 := by
  rw [Real.exp_neg, show Real.exp 66 = Real.exp 1 ^ 66 by rw [← Real.exp_nat_mul]; norm_num, one_div]
  refine inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) ?_ 66)
  have := Real.exp_one_gt_d9; linarith

theorem harmHead_eq : ∑ k ∈ Finset.Icc (7 : ℕ) 30, 1 / (2 * (k : ℝ)) =
    ∑ k ∈ ({7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30} : Finset ℕ), 1 / (2 * (k : ℝ)) := by
  congr 1

/-- **Numerical comparison at field `2000`.** The lower bound for the free harmonic magnetization
from `k = 7` exceeds the Gamma upper bound for the Riemann magnetization by more than `1/200`. -/
theorem harm_minus_gamma_gt (N : ℕ) (hN : 1000000 ≤ N) :
    1 / (1 / 2 + 2000) + 1 / (2000 - 1 / 2) - Real.log Real.pi / 2 +
        Real.log ((1 / 2 + 2000) / 2) / 2 + 1 / 200 <
      (∑ k ∈ Finset.Icc (7 : ℕ) 30, 1 / (2 * (k : ℝ))) - 24 * Real.exp (-66) / 7 +
        ((Real.log 1000 - Real.log 31) / 2 -
          ((Real.exp (-2) - Real.exp (-3)) / 2 + Real.exp (-3) / 3)) +
        (4 / 9 - 500 / ((N + 1 : ℕ) : ℝ)) := by
  have hN' : (1000001 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 1000001 ≤ N + 1)
  have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by linarith
  have h500 : 500 / ((N + 1 : ℕ) : ℝ) ≤ 500 / 1000001 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have hlog1000 : Real.log ((1 / 2 + 2000) / 2) ≤ Real.log 1000 + 1 / 4000 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((1 / 2 + 2000) / 2) / 1000 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have h31 := log_thirtyOne_le
  have hpi := log_pi_ge
  have he2 := exp_neg_two_le
  have he3 := exp_neg_three_ge
  have he66 := exp_neg_sixtySix_le
  have hhead : ∑ k ∈ Finset.Icc (7 : ℕ) 30, 1 / (2 * (k : ℝ)) ≥ 0.7724935 := by
    rw [harmHead_eq]; norm_num [Finset.sum_insert]
  have hsmall : 1 / (1 / 2 + 2000 : ℝ) + 1 / (2000 - 1 / 2) ≤ 0.0010001 := by norm_num
  norm_num at h31 he2 he3 he66
  linarith

end RHTower.GriffithsSimon


namespace RHTower.GriffithsSimon

open Set

/-- **The harmonic Griffiths–Simon program fails from `K ≤ 7`.** Take finite ferromagnetic Ising
systems (`J ≥ 0`, masses `c ≥ 0`) that contain, injectively, spins of mass `1/(2k)` for every
`K ≤ k ≤ N_n`, with `N_n → ∞`. If `K ≤ 7`, their centred characteristic functions do not converge
locally uniformly to `Ξ(z)/Ξ(0)`.

The proof compares magnetizations at the field `w = 2000`. Griffiths' inequality forces the
producer's magnetization to dominate the free value `Σ_{k=7}^{N} tanh(1000/k)/(2k)`. The Gamma
bound `(ξ'/ξ)(½+w) ≤ 1/(½+w) + 1/(w−½) − (log π)/2 + (log((½+w)/2))/2` caps the limit. The free
harmonic sum exceeds the cap by more than `1/200`. -/
theorem not_tendstoLocallyUniformly_harmonic_isingChar {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    {K : ℕ} (hK : K ≤ 7) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (e : ∀ n, Finset.Icc K (N n) → ι n) (he : ∀ n, Function.Injective (e n))
    (hce : ∀ n (k : Finset.Icc K (N n)), c n (e n k) = 1 / (2 * ((k : ℕ) : ℝ))) :
    ¬ TendstoLocallyUniformly (fun n => isingChar (J n) (E n) (c n))
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hev := eventually_freeMag_le_xiRealLogDeriv J E hJ c hc hconv (w := 2000) (by norm_num)
    (ε := 1 / 200) (by norm_num)
  obtain ⟨n, hn, hNn⟩ := (hev.and (hN.eventually (eventually_ge_atTop 1000000))).exists
  have hcap := xiRealLogDeriv_le (w := 2000) (by norm_num)
  have hgap := harm_minus_gamma_gt (N n) hNn
  have hlow := harmSum_ge (N n) (by omega)
  -- the producer's free magnetization dominates the harmonic sum
  have hterm_nonneg : ∀ v, 0 ≤ c n v * Real.tanh (c n v * 2000) := fun v =>
    mul_nonneg (hc n v) (tanh_nonneg_of_nonneg (mul_nonneg (hc n v) (by norm_num)))
  have hsub : ∑ k ∈ Finset.Icc 7 (N n), harmTerm k ≤ ∑ k ∈ Finset.Icc K (N n), harmTerm k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · unfold harmTerm
      exact div_nonneg (tanh_nonneg_of_nonneg (by positivity)) (by positivity)
  have hemb : ∑ k ∈ Finset.Icc K (N n), harmTerm k ≤ ∑ v, c n v * Real.tanh (c n v * 2000) := by
    rw [← Finset.sum_coe_sort (Finset.Icc K (N n))]
    have himg := Finset.sum_image (s := (Finset.univ : Finset (Finset.Icc K (N n))))
      (g := e n) (f := fun v => c n v * Real.tanh (c n v * 2000))
      (fun a _ b _ hab => he n hab)
    calc ∑ k : Finset.Icc K (N n), harmTerm ((k : ℕ) : ℝ)
        = ∑ k : Finset.Icc K (N n), c n (e n k) * Real.tanh (c n (e n k) * 2000) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hce n k]
          unfold harmTerm
          rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | hpos
          · rw [h0]; simp
          · have hk0 : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hpos
            rw [show 1 / (2 * ((k : ℕ) : ℝ)) * 2000 = 1000 / ((k : ℕ) : ℝ) by field_simp; ring]
            field_simp
      _ = ∑ v ∈ Finset.univ.image (e n), c n v * Real.tanh (c n v * 2000) := himg.symm
      _ ≤ ∑ v, c n v * Real.tanh (c n v * 2000) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ => hterm_nonneg v
  linarith

end RHTower.GriffithsSimon
