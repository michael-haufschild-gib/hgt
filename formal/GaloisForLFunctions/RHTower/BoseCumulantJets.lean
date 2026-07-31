import GaloisForLFunctions.RHTower.BoseMellinCoordinate
import GaloisForLFunctions.HTGeometry.RealAnalyticTransfer

/-!
# The completed Xi jets as Bose cumulant differences

On the real ray the completed Xi function factors as

`xi (1+a) = (1+a) * 2^(-a) * pi^(-a/2) * M a / Gamma (a/2)`,

so its logarithm is the sum of an elementary rational term, one affine term, the Bose
log-normalizer `log (M a)` and the half-Gamma term `- log (Gamma (a/2))`.  Differentiating the
logarithm therefore expresses every completed Xi jet as

`rational jet - half-Gamma jet + Bose cumulant`,

with the affine term surviving only at order one, where it contributes exactly `- log (2 sqrt pi)`.
Writing `kappa_r a = (d/da)^r log (M a)` — the exponential-family definition of the Bose-log
cumulants — this is the card's pair of jet identities.

The real smoothness of every factor is supplied by holomorphy: `Gamma` and `zeta` are holomorphic
on the rays used here, so their restrictions to the real axis are smooth by
`contDiffAt_re_comp_ofReal`.
-/

open Set Filter

namespace RHTower

noncomputable section

/-! ### Real smoothness of the Gamma and zeta factors -/

theorem contDiffAt_realGamma {x : ℝ} (hx : 0 < x) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n Real.Gamma x := by
  have hs : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hmz
    have hre := congrArg Complex.re hmz
    rw [Complex.neg_re, Complex.natCast_re] at hre
    have hzre : (0:ℝ) < z.re := hz
    have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hx' : ((x : ℂ)) ∈ {z : ℂ | 0 < z.re} := by
    simpa using hx
  have h := GaloisForLFunctions.HTGeometry.contDiffAt_re_comp_ofReal hs hdiff hx' n
  have hfun : (fun y : ℝ => (Complex.Gamma ((y : ℝ) : ℂ)).re) = Real.Gamma := by
    funext y
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rwa [hfun] at h

theorem contDiffAt_realZetaSeries {x : ℝ} (hx : 1 < x) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n realZetaSeries x := by
  have hs : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | 1 < z.re} := by
    intro z hz
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro h
    rw [h] at hz
    simp only [mem_setOf_eq, Complex.one_re, lt_self_iff_false] at hz
  have hx' : ((x : ℂ)) ∈ {z : ℂ | 1 < z.re} := by
    simpa using hx
  have h := GaloisForLFunctions.HTGeometry.contDiffAt_re_comp_ofReal hs hdiff hx' n
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [← ofReal_realZetaSeries (s := y) hy, Complex.ofReal_re]

theorem contDiffAt_shift (c : ℝ) (a : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => b + c) a :=
  (contDiff_id.add contDiff_const).contDiffAt

theorem contDiffAt_boseMellin {a : ℝ} (ha : 0 < a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n boseMellin a := by
  have h1 : ContDiffAt ℝ n (fun b : ℝ => Real.Gamma (b + 1)) a :=
    ContDiffAt.comp (f := fun b : ℝ => b + 1) a
      (contDiffAt_realGamma (show (0:ℝ) < a + 1 by linarith) n) (contDiffAt_shift 1 a n)
  have h2 : ContDiffAt ℝ n (fun b : ℝ => realZetaSeries (b + 1)) a :=
    ContDiffAt.comp (f := fun b : ℝ => b + 1) a
      (contDiffAt_realZetaSeries (show (1:ℝ) < a + 1 by linarith) n) (contDiffAt_shift 1 a n)
  refine (h1.mul h2).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact boseMellin_eq hb

theorem contDiffAt_logBoseMellin {a : ℝ} (ha : 0 < a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => Real.log (boseMellin b)) a :=
  (contDiffAt_boseMellin ha n).log (ne_of_gt (boseMellin_pos ha))

theorem contDiffAt_logGammaHalf {a : ℝ} (ha : 0 < a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => Real.log (Real.Gamma (b / 2))) a := by
  have hhalf : ContDiffAt ℝ n (fun b : ℝ => b / 2) a := by
    have : ContDiff ℝ n (fun b : ℝ => b / 2) := by
      simpa [div_eq_mul_inv] using (contDiff_id (𝕜 := ℝ) (E := ℝ) (n := n)).mul contDiff_const
    exact this.contDiffAt
  have hinner : ContDiffAt ℝ n (fun b : ℝ => Real.Gamma (b / 2)) a :=
    ContDiffAt.comp (f := fun b : ℝ => b / 2) a
      (contDiffAt_realGamma (show (0:ℝ) < a / 2 by linarith) n) hhalf
  exact hinner.log (ne_of_gt (Real.Gamma_pos_of_pos (by linarith)))

theorem contDiffAt_logOneAdd {a : ℝ} (ha : -1 < a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => Real.log (1 + b)) a := by
  have hinner : ContDiffAt ℝ n (fun b : ℝ => 1 + b) a := by
    have : ContDiff ℝ n (fun b : ℝ => 1 + b) := contDiff_const.add contDiff_id
    exact this.contDiffAt
  exact hinner.log (by intro h; linarith [h])

theorem contDiffAt_linear (c : ℝ) (a : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => c * b) a :=
  (contDiff_const.mul contDiff_id).contDiffAt

/-! ### Iterated derivatives of the elementary terms -/

theorem iteratedDeriv_const_eq_zero (m : ℕ) (c : ℝ) :
    ∀ x : ℝ, iteratedDeriv (m + 1) (fun _ : ℝ => c) x = 0 := by
  induction m with
  | zero =>
      intro x
      rw [iteratedDeriv_one]
      exact deriv_const x c
  | succ k ih =>
      intro x
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv (k + 1) (fun _ : ℝ => c) = fun _ : ℝ => (0:ℝ) := by
        funext y
        exact ih y
      rw [hfun]
      exact deriv_const x 0

theorem iteratedDeriv_linear_eq_zero (c : ℝ) (m : ℕ) (x : ℝ) :
    iteratedDeriv (m + 2) (fun b : ℝ => c * b) x = 0 := by
  rw [iteratedDeriv_succ']
  have hfun : deriv (fun b : ℝ => c * b) = fun _ : ℝ => c := by
    funext y
    simp
  rw [hfun]
  exact iteratedDeriv_const_eq_zero m c x

/-- The rational jet `(-1)^j j! / (1+a)^(j+1)` of `log (1+a)`. -/
def onePlusJet (j : ℕ) (a : ℝ) : ℝ :=
  (-1 : ℝ) ^ j * (j.factorial : ℝ) * ((1 + a) ^ (j + 1))⁻¹

theorem hasDerivAt_onePlusJet (j : ℕ) {a : ℝ} (ha : -1 < a) :
    HasDerivAt (onePlusJet j) (onePlusJet (j + 1) a) a := by
  have hpos : (0:ℝ) < 1 + a := by linarith
  have hne : ((1 + a) ^ (j + 1)) ≠ 0 := by positivity
  have hbase : HasDerivAt (fun x : ℝ => 1 + x) 1 a :=
    HasDerivAt.const_add (1:ℝ) (hasDerivAt_id a)
  have hpow := hbase.pow (j + 1)
  simp only [Nat.add_sub_cancel, mul_one] at hpow
  have hinv := hpow.inv hne
  have hres := hinv.const_mul ((-1 : ℝ) ^ j * (j.factorial : ℝ))
  have hval : ((-1 : ℝ) ^ j * (j.factorial : ℝ)) *
      (-(((j + 1 : ℕ) : ℝ) * (1 + a) ^ j) / ((1 + a) ^ (j + 1)) ^ 2)
      = onePlusJet (j + 1) a := by
    rw [onePlusJet]
    push_cast [Nat.factorial_succ]
    field_simp
    ring
  rw [← hval]
  exact hres

theorem iteratedDeriv_logOneAdd (j : ℕ) :
    ∀ {a : ℝ}, -1 < a →
      iteratedDeriv (j + 1) (fun b : ℝ => Real.log (1 + b)) a = onePlusJet j a := by
  induction j with
  | zero =>
      intro a ha
      have hb : HasDerivAt (fun b : ℝ => 1 + b) 1 a :=
        HasDerivAt.const_add (1:ℝ) (hasDerivAt_id a)
      have h := hb.log (by intro hz; linarith [hz])
      rw [iteratedDeriv_one, h.deriv, onePlusJet]
      simp
  | succ j ih =>
      intro a ha
      have hEq : iteratedDeriv (j + 1) (fun b : ℝ => Real.log (1 + b))
          =ᶠ[nhds a] onePlusJet j := by
        filter_upwards [Ioi_mem_nhds ha] with b hb using ih hb
      rw [iteratedDeriv_succ, hEq.deriv_eq, (hasDerivAt_onePlusJet j ha).deriv]

/-! ### The logarithm of the completed Xi factorization -/

/-- The completed Xi value on the real ray, in Bose coordinates. -/
def xiRealRay (a : ℝ) : ℝ :=
  (1 + a) * (2 : ℝ) ^ (-a) * Real.pi ^ (-a / 2) * boseMellin a / Real.Gamma (a / 2)

theorem xi_ofReal_one_add_eq_xiRealRay {a : ℝ} (ha : 0 < a) :
    xi (((1 + a : ℝ) : ℂ)) = ((xiRealRay a : ℝ) : ℂ) :=
  xi_ofReal_one_add_eq_boseMellin ha

theorem xiRealRay_pos {a : ℝ} (ha : 0 < a) : 0 < xiRealRay a := by
  have h1 : (0:ℝ) < 1 + a := by linarith
  have h2 : (0:ℝ) < (2:ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (0:ℝ) < Real.pi ^ (-a / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h4 : (0:ℝ) < boseMellin a := boseMellin_pos ha
  have h5 : (0:ℝ) < Real.Gamma (a / 2) := Real.Gamma_pos_of_pos (by linarith)
  rw [xiRealRay]
  positivity

/-- The additive decomposition of `log (xi (1+a))` on the real ray. -/
def boseXiLogJetBase (a : ℝ) : ℝ :=
  Real.log (1 + a) - (Real.log 2 + Real.log Real.pi / 2) * a
    + Real.log (boseMellin a) - Real.log (Real.Gamma (a / 2))

theorem log_xiRealRay {a : ℝ} (ha : 0 < a) :
    Real.log (xiRealRay a) = boseXiLogJetBase a := by
  have h1 : (0:ℝ) < 1 + a := by linarith
  have h2 : (0:ℝ) < (2:ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (0:ℝ) < Real.pi ^ (-a / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h4 : (0:ℝ) < boseMellin a := boseMellin_pos ha
  have h5 : (0:ℝ) < Real.Gamma (a / 2) := Real.Gamma_pos_of_pos (by linarith)
  rw [xiRealRay, Real.log_div (by positivity) (ne_of_gt h5),
    Real.log_mul (by positivity) (ne_of_gt h4),
    Real.log_mul (by positivity) (ne_of_gt h3),
    Real.log_mul (ne_of_gt h1) (ne_of_gt h2),
    Real.log_rpow (by norm_num), Real.log_rpow Real.pi_pos, boseXiLogJetBase]
  ring

theorem contDiffAt_boseXiLogJetBase {a : ℝ} (ha : 0 < a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n boseXiLogJetBase a := by
  have h1 : ContDiffAt ℝ n (fun b : ℝ => Real.log (1 + b)) a :=
    contDiffAt_logOneAdd (by linarith) n
  have h2 : ContDiffAt ℝ n (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b) a :=
    contDiffAt_linear _ a n
  have h3 : ContDiffAt ℝ n (fun b : ℝ => Real.log (boseMellin b)) a :=
    contDiffAt_logBoseMellin ha n
  have h4 : ContDiffAt ℝ n (fun b : ℝ => Real.log (Real.Gamma (b / 2))) a :=
    contDiffAt_logGammaHalf ha n
  exact ((h1.sub h2).add h3).sub h4

/-! ### The jet identities -/

/-- **Order-one jet.**  This is the card's equation `(5)`: the affine term contributes exactly
`- log (2 sqrt pi) = - log 2 - (log pi)/2`. -/
theorem iteratedDeriv_one_boseXiLogJetBase {a : ℝ} (ha : 0 < a) :
    iteratedDeriv 1 boseXiLogJetBase a
      = 1 / (1 + a) - (Real.log 2 + Real.log Real.pi / 2)
        + iteratedDeriv 1 (fun b : ℝ => Real.log (boseMellin b)) a
        - iteratedDeriv 1 (fun b : ℝ => Real.log (Real.Gamma (b / 2))) a := by
  have h1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun b : ℝ => Real.log (1 + b)) a :=
    contDiffAt_logOneAdd (by linarith) _
  have h2 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b) a := contDiffAt_linear _ a _
  have h3 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun b : ℝ => Real.log (boseMellin b)) a := contDiffAt_logBoseMellin ha _
  have h4 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun b : ℝ => Real.log (Real.Gamma (b / 2))) a := contDiffAt_logGammaHalf ha _
  have hA : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      ((fun b : ℝ => Real.log (1 + b))
        - (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b)) a := h1.sub h2
  have hB : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (((fun b : ℝ => Real.log (1 + b))
        - (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b))
        + (fun b : ℝ => Real.log (boseMellin b))) a := hA.add h3
  have hbase : boseXiLogJetBase =
      (((fun b : ℝ => Real.log (1 + b))
        - (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b))
        + (fun b : ℝ => Real.log (boseMellin b)))
        - (fun b : ℝ => Real.log (Real.Gamma (b / 2))) := rfl
  have hlin : iteratedDeriv 1 (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b) a
      = Real.log 2 + Real.log Real.pi / 2 := by
    rw [iteratedDeriv_one]
    simp
  have hrat : iteratedDeriv 1 (fun b : ℝ => Real.log (1 + b)) a = 1 / (1 + a) := by
    have hb : HasDerivAt (fun b : ℝ => 1 + b) 1 a :=
      HasDerivAt.const_add (1:ℝ) (hasDerivAt_id a)
    have h := hb.log (by intro hz; linarith [hz])
    rw [iteratedDeriv_one, h.deriv]
  rw [hbase, iteratedDeriv_sub hB h4, iteratedDeriv_add hA h3,
    iteratedDeriv_sub h1 h2, hrat, hlin]

theorem deriv_boseXiLogJetBase {a : ℝ} (ha : 0 < a) :
    deriv boseXiLogJetBase a
      = 1 / (1 + a) - (Real.log 2 + Real.log Real.pi / 2)
        + deriv (fun b : ℝ => Real.log (boseMellin b)) a
        - deriv (fun b : ℝ => Real.log (Real.Gamma (b / 2))) a := by
  have h := iteratedDeriv_one_boseXiLogJetBase ha
  rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_one] at h
  exact h

/-- **Higher jets.**  This is the card's equation `(6)`: from order two on the affine term has
disappeared, and every completed Xi jet is the rational jet plus the Bose cumulant minus the
half-Gamma jet. -/
theorem iteratedDeriv_boseXiLogJetBase {m : ℕ} (hm : 2 ≤ m) {a : ℝ} (ha : 0 < a) :
    iteratedDeriv m boseXiLogJetBase a
      = onePlusJet (m - 1) a
        + iteratedDeriv m (fun b : ℝ => Real.log (boseMellin b)) a
        - iteratedDeriv m (fun b : ℝ => Real.log (Real.Gamma (b / 2))) a := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun b : ℝ => Real.log (1 + b)) a :=
    contDiffAt_logOneAdd (by linarith) _
  have h2 : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b) a := contDiffAt_linear _ a _
  have h3 : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (fun b : ℝ => Real.log (boseMellin b)) a := contDiffAt_logBoseMellin ha _
  have h4 : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (fun b : ℝ => Real.log (Real.Gamma (b / 2))) a := contDiffAt_logGammaHalf ha _
  have hA : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      ((fun b : ℝ => Real.log (1 + b))
        - (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b)) a := h1.sub h2
  have hB : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (((fun b : ℝ => Real.log (1 + b))
        - (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b))
        + (fun b : ℝ => Real.log (boseMellin b))) a := hA.add h3
  have hbase : boseXiLogJetBase =
      (((fun b : ℝ => Real.log (1 + b))
        - (fun b : ℝ => (Real.log 2 + Real.log Real.pi / 2) * b))
        + (fun b : ℝ => Real.log (boseMellin b)))
        - (fun b : ℝ => Real.log (Real.Gamma (b / 2))) := rfl
  rw [hbase, iteratedDeriv_sub hB h4, iteratedDeriv_add hA h3,
    iteratedDeriv_sub h1 h2,
    iteratedDeriv_linear_eq_zero _ k a, iteratedDeriv_logOneAdd (k + 1) (by linarith)]
  simp

/-! ### The cumulant split -/

theorem contDiffAt_logGammaShift {a : ℝ} (ha : 0 < a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => Real.log (Real.Gamma (b + 1))) a :=
  (ContDiffAt.comp (f := fun b : ℝ => b + 1) a
    (contDiffAt_realGamma (show (0:ℝ) < a + 1 by linarith) n) (contDiffAt_shift 1 a n)).log
    (ne_of_gt (Real.Gamma_pos_of_pos (by linarith)))

theorem contDiffAt_logZetaShift {a : ℝ} (ha : 0 < a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => Real.log (realZetaSeries (b + 1))) a :=
  (ContDiffAt.comp (f := fun b : ℝ => b + 1) a
    (contDiffAt_realZetaSeries (show (1:ℝ) < a + 1 by linarith) n) (contDiffAt_shift 1 a n)).log
    (ne_of_gt (realZetaSeries_pos (by linarith)))

/-- **The Bose cumulants split.**  Equation `(11)`: `log (M a) = log (Gamma (a+1)) +
log (zeta (a+1))`, so every Bose-log cumulant is a Gamma jet plus a zeta jet. -/
theorem iteratedDeriv_logBoseMellin (r : ℕ) {a : ℝ} (ha : 0 < a) :
    iteratedDeriv r (fun b : ℝ => Real.log (boseMellin b)) a
      = iteratedDeriv r (fun b : ℝ => Real.log (Real.Gamma (b + 1))) a
        + iteratedDeriv r (fun b : ℝ => Real.log (realZetaSeries (b + 1))) a := by
  have hEq : (fun b : ℝ => Real.log (boseMellin b))
      =ᶠ[nhds a] ((fun b : ℝ => Real.log (Real.Gamma (b + 1)))
        + (fun b : ℝ => Real.log (realZetaSeries (b + 1)))) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    have hb' : (0:ℝ) < b := hb
    rw [boseMellin_eq hb', Real.log_mul (ne_of_gt (Real.Gamma_pos_of_pos (by linarith)))
      (ne_of_gt (realZetaSeries_pos (by linarith)))]
    rfl
  rw [Filter.EventuallyEq.iteratedDeriv_eq r hEq,
    iteratedDeriv_add (contDiffAt_logGammaShift ha _) (contDiffAt_logZetaShift ha _)]

end

end RHTower
