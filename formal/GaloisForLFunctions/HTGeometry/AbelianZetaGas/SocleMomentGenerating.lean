import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleResponse
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ClassLaw
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCharFun
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Normalization

/-!
# The socle moment generating function of the abelian zeta gas

For the socle observable `Q(A) = log |soc A|` and a gas state `(σ, τ)`,

  `E_{σ,τ} e^{-zQ} = ∏_{j≥1} ζ(jσ + τ + z) / ∏_{j≥1} ζ(jσ + τ)`

whenever `σ + τ + Re z > 1`, i.e. for the full complex half-plane where the right side is an
absolutely convergent product.  The proof runs through the mode product structure of the gas: the
socle is the mode-additive functional `∑_m N_m log p`, a finite truncation factors into
independent geometric moment generating functions, and the infinite product is regrouped into the
complex Euler products of the socle ladder.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

/-! ## Complex Euler regrouping of the socle ladder -/

/-- The mode Euler factor `1 - p^{-((n+1)σ + v)}` of the socle ladder. -/
def modeEulerFactor (σ : ℝ) (v : ℂ) (m : AbelianZetaMode) : ℂ :=
  1 - ((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v))

theorem norm_mode_cpow (σ : ℝ) (v : ℂ) (m : AbelianZetaMode) :
    ‖((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v))‖ = abelianZetaTailRatio σ v.re 1 m := by
  rw [Complex.norm_natCast_cpow_of_pos m.1.prop.pos, abelianZetaTailRatio]
  congr 1
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.ofReal_re, Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero]
  push_cast
  ring

theorem summable_norm_mode_cpow {σ : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : 1 < σ + v.re) :
    Summable fun m : AbelianZetaMode =>
      ‖((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v))‖ := by
  simp_rw [norm_mode_cpow]
  exact summable_abelianZetaTailRatio hσ (g := 1) (by simpa using hv)

theorem norm_mode_cpow_lt_one {σ : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : 1 < σ + v.re)
    (m : AbelianZetaMode) : ‖((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v))‖ < 1 := by
  rw [norm_mode_cpow, abelianZetaTailRatio]
  refine Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast m.1.prop.one_lt) ?_
  have hn : (0 : ℝ) ≤ (m.2 : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem modeEulerFactor_ne_zero {σ : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : 1 < σ + v.re)
    (m : AbelianZetaMode) : modeEulerFactor σ v m ≠ 0 := by
  intro h
  have h1 : ((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v)) = 1 := by
    rw [modeEulerFactor, sub_eq_zero] at h
    exact h.symm
  have := norm_mode_cpow_lt_one hσ hv m
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem hasProd_inv_of_ne_zero {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  rw [HasProd] at h ⊢
  simpa only [Finset.prod_inv_distrib] using h.inv₀ ha

theorem hasProd_prime_modeEulerFactor {σ : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : 1 < σ + v.re) (n : ℕ) :
    HasProd (fun p : Nat.Primes => modeEulerFactor σ v (p, n))
      (riemannZeta (((n + 1 : ℕ) : ℂ) * σ + v))⁻¹ := by
  set s : ℂ := ((n + 1 : ℕ) : ℂ) * σ + v with hsdef
  have hs : 1 < s.re := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    simp only [hsdef, Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
      Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero]
    push_cast
    nlinarith
  have h := hasProd_inv_of_ne_zero (riemannZeta_eulerProduct_hasProd hs)
    (riemannZeta_ne_zero_of_one_lt_re hs)
  convert h using 1
  funext p
  simp only [modeEulerFactor, inv_inv, hsdef]

/-- **Complex Euler regrouping.**  `∏_m (1 - p^{-((n+1)σ + v)}) = (∏_{j≥1} ζ(jσ + v))⁻¹` for
`σ + Re v > 1`. -/
theorem hasProd_modeEulerFactor {σ : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : 1 < σ + v.re) :
    HasProd (modeEulerFactor σ v) (socleLadder σ v)⁻¹ := by
  have hsum : Summable fun m : AbelianZetaMode =>
      -(((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v))) :=
    (summable_norm_mode_cpow hσ hv).of_norm.neg
  have hfun : modeEulerFactor σ v = fun m : AbelianZetaMode =>
      1 + -(((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v))) := by
    funext m
    rw [modeEulerFactor, sub_eq_add_neg]
  have hmul : Multipliable (modeEulerFactor σ v) := by
    rw [hfun]
    exact Complex.multipliable_one_add_of_summable hsum
  have hreindexed : HasProd (fun x : ℕ × Nat.Primes => modeEulerFactor σ v (x.2, x.1))
      (∏' m, modeEulerFactor σ v m) :=
    ((Equiv.prodComm ℕ Nat.Primes).hasProd_iff).2 hmul.hasProd
  have houter : HasProd (fun n : ℕ => (riemannZeta (((n + 1 : ℕ) : ℂ) * σ + v))⁻¹)
      (∏' m, modeEulerFactor σ v m) :=
    hreindexed.prod_fiberwise fun n => hasProd_prime_modeEulerFactor hσ hv n
  have hne : (∏' m, modeEulerFactor σ v m) ≠ 0 := by
    have := tprod_one_add_ne_zero_of_summable
      (f := fun m : AbelianZetaMode => -(((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * σ + v))))
      (fun m => by rw [← sub_eq_add_neg]; exact modeEulerFactor_ne_zero hσ hv m)
      (by simpa only [norm_neg] using summable_norm_mode_cpow hσ hv)
    simpa only [modeEulerFactor, sub_eq_add_neg] using this
  have hzeta := hasProd_inv_of_ne_zero houter hne
  simp only [inv_inv] at hzeta
  have hladder : socleLadder σ v = (∏' m, modeEulerFactor σ v m)⁻¹ := by
    rw [socleLadder_eq_tprod, hzeta.tprod_eq]
  rw [hladder, inv_inv]
  exact hmul.hasProd

/-! ## Mode moment generating functions -/

/-- The socle observable `Q(A) = log |soc A|`. -/
def socleLog (A : AbelianZetaGroupClass) : ℝ := Real.log ((A.socleOrder : ℕ) : ℝ)

theorem socleLog_nonneg (A : AbelianZetaGroupClass) : 0 ≤ socleLog A :=
  Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    rw [AbelianZetaGroupClass.socleOrder, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => pow_ne_zero _ m.1.prop.ne_zero))

theorem ratio_eq_norm_mode_cpow (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    (θ.ratio m : ℂ) = ((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * θ.sigma + θ.tau)) := by
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent,
    Complex.ofReal_cpow (by exact_mod_cast m.1.prop.pos.le)]
  congr 1
  simp [AbelianZetaMode.depth]

/-- The mode moment generating function at a complex exponent. -/
theorem integral_modeLaw_cexp (θ : AbelianZetaParameters) (m : AbelianZetaMode) (w : ℂ)
    (hw : θ.ratio m * Real.exp w.re < 1) :
    ∫ n : ℕ, Complex.exp (w * n) ∂(θ.modeLaw m) =
      (1 - (θ.ratio m : ℂ)) / (1 - (θ.ratio m : ℂ) * Complex.exp w) := by
  have hq0 : (0 : ℝ) < θ.ratio m := θ.ratio_pos m
  have hsucc : ((θ.success m : ℝ)) = 1 - θ.ratio m := by
    have := θ.one_sub_success m
    linarith
  have hnorm : ‖(θ.ratio m : ℂ) * Complex.exp w‖ < 1 := by
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    exact hw
  rw [AbelianZetaParameters.modeLaw, integral_geometricMeasure (θ.success_ne_zero m)]
  have hterm : ∀ n : ℕ,
      ((1 - (θ.success m : ℝ)) ^ n * (θ.success m : ℝ)) • Complex.exp (w * n)
        = (1 - (θ.ratio m : ℂ)) * ((θ.ratio m : ℂ) * Complex.exp w) ^ n := by
    intro n
    have hexp : Complex.exp (w * n) = Complex.exp w ^ n := by
      rw [← Complex.exp_nat_mul, mul_comm]
    rw [hexp, mul_pow, hsucc, Complex.real_smul]
    push_cast
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm, div_eq_mul_inv]

theorem integrable_modeLaw_cexp (θ : AbelianZetaParameters) (m : AbelianZetaMode) (w : ℂ)
    (hw : θ.ratio m * Real.exp w.re < 1) :
    Integrable (fun n : ℕ => Complex.exp (w * n)) (θ.modeLaw m) := by
  rw [AbelianZetaParameters.modeLaw, integrable_geometricMeasure_iff (θ.success_ne_zero m)]
  have hsucc : ((θ.success m : ℝ)) = 1 - θ.ratio m := by
    have := θ.one_sub_success m
    linarith
  have hq : 0 ≤ θ.ratio m * Real.exp w.re := by positivity [θ.ratio_pos m]
  have hgeo : Summable fun n : ℕ => (θ.ratio m * Real.exp w.re) ^ n :=
    summable_geometric_of_lt_one hq hw
  refine (hgeo.mul_left (1 - θ.ratio m)).congr fun n => ?_
  have hn : ‖Complex.exp (w * n)‖ = Real.exp w.re ^ n := by
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    ring
  rw [hn, hsucc, sub_sub_cancel]
  ring

theorem integral_gasMeasure_cexp_finset (θ : AbelianZetaParameters) (w : AbelianZetaMode → ℂ)
    (s : Finset AbelianZetaMode) (hw : ∀ m, θ.ratio m * Real.exp (w m).re < 1) :
    ∫ k, Complex.exp (∑ m ∈ s, w m * k m) ∂θ.gasMeasure =
      ∏ m ∈ s, (1 - (θ.ratio m : ℂ)) / (1 - (θ.ratio m : ℂ) * Complex.exp (w m)) := by
  classical
  have hindep : iIndepFun (fun (m : s) (k : AbelianZetaMode → ℕ) => k (m : AbelianZetaMode))
      θ.gasMeasure := (θ.iIndepFun_eval).precomp Subtype.coe_injective
  have hsplit : ∀ k : AbelianZetaMode → ℕ,
      Complex.exp (∑ m ∈ s, w m * k m) =
        ∏ m : s, Complex.exp (w (m : AbelianZetaMode) * k (m : AbelianZetaMode)) := by
    intro k
    rw [Complex.exp_sum, ← Finset.prod_coe_sort s (fun m => Complex.exp (w m * k m))]
  simp only [hsplit]
  rw [hindep.integral_fun_prod_comp
    (f := fun (m : s) (n : ℕ) => Complex.exp (w (m : AbelianZetaMode) * n))
    (fun _ => (measurable_pi_apply _).aemeasurable)
    (fun _ => (measurable_from_top).aestronglyMeasurable)]
  rw [← Finset.prod_coe_sort s (fun m => (1 - (θ.ratio m : ℂ))
    / (1 - (θ.ratio m : ℂ) * Complex.exp (w m)))]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [θ.integral_gasMeasure_eval (m : AbelianZetaMode)
    (fun n => Complex.exp (w (m : AbelianZetaMode) * n)), integral_modeLaw_cexp θ _ _ (hw _)]

/-! ## Truncated socle observables -/

/-- The enumeration of modes used for truncation. -/
abbrev modeAt (i : ℕ) : AbelianZetaMode := AbelianZetaParameters.modeEquivNat i

/-- The socle contribution `∑_{i<N} N_{m_i} log p_{m_i}` of the first `N` enumerated modes. -/
def truncSocle (N : ℕ) (k : AbelianZetaMode → ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (k (modeAt i) : ℝ) * Real.log (((modeAt i).1 : ℕ) : ℝ)

theorem log_prime_nonneg' (m : AbelianZetaMode) : 0 ≤ Real.log (((m.1 : ℕ) : ℝ)) :=
  Real.log_nonneg (by exact_mod_cast m.1.prop.one_lt.le)

theorem truncSocle_nonneg (N : ℕ) (k : AbelianZetaMode → ℕ) : 0 ≤ truncSocle N k :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (log_prime_nonneg' _)

theorem truncSocle_mono (k : AbelianZetaMode → ℕ) : Monotone fun N => truncSocle N k :=
  monotone_nat_of_le_succ fun N => by
    simp only [truncSocle, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (log_prime_nonneg' _))

theorem measurable_truncSocle (N : ℕ) : Measurable (truncSocle N) :=
  Finset.measurable_sum _ fun i _ =>
    ((measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp
      (measurable_pi_apply (modeAt i))).mul_const _

theorem eventually_truncSocle_eq {k : AbelianZetaMode → ℕ} (hk : (Function.support k).Finite) :
    ∀ᶠ N in atTop, truncSocle N k = socleLog (classOf k) := by
  classical
  set S := (classOf k).support
  set e := AbelianZetaParameters.modeEquivNat
  refine (eventually_ge_atTop (S.sup fun m => e.symm m + 1)).mono fun N hN => ?_
  have hsub : S ⊆ (Finset.range N).map e.toEmbedding := fun m hm => by
    rw [Finset.mem_map]
    refine ⟨e.symm m, Finset.mem_range.mpr ?_, by simp⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      ((Finset.le_sup (f := fun m => e.symm m + 1) hm).trans hN)
  have hval := classOf_of_finite hk
  rw [socleLog, log_socleOrder_classOf hk, truncSocle]
  rw [show (∑ i ∈ Finset.range N, (k (modeAt i) : ℝ) * Real.log (((modeAt i).1 : ℕ) : ℝ)) =
      ∑ m ∈ (Finset.range N).map e.toEmbedding, (k m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)) by
    rw [Finset.sum_map]
    rfl]
  refine (Finset.sum_subset hsub fun m _ hm => ?_).symm
  have hkm : k m = 0 := by
    rw [← congrFun hval m]
    exact Finsupp.notMem_support_iff.mp hm
  rw [hkm, Nat.cast_zero, zero_mul]

theorem tendsto_truncSocle {k : AbelianZetaMode → ℕ} (hk : (Function.support k).Finite) :
    Tendsto (fun N => truncSocle N k) atTop (𝓝 (socleLog (classOf k))) :=
  tendsto_const_nhds.congr' (EventuallyEq.symm (eventually_truncSocle_eq hk))

theorem truncSocle_le_socleLog {k : AbelianZetaMode → ℕ} (hk : (Function.support k).Finite)
    (N : ℕ) : truncSocle N k ≤ socleLog (classOf k) :=
  (truncSocle_mono k).ge_of_tendsto (tendsto_truncSocle hk) N

/-! ## The moment generating function of the gas -/

section Gas

variable (θ : AbelianZetaConvergentParameters)

/-- The mode factor `(1 - r_m)/(1 - r_m p^{-z})` of the socle moment generating function. -/
def socleModeFactor (z : ℂ) (m : AbelianZetaMode) : ℂ :=
  (1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) /
    (1 - (θ.toAbelianZetaParameters.ratio m : ℂ) *
      Complex.exp (-z * Real.log (((m.1 : ℕ) : ℝ))))

theorem ratio_mul_cexp (z : ℂ) (m : AbelianZetaMode) :
    (θ.toAbelianZetaParameters.ratio m : ℂ) * Complex.exp (-z * Real.log (((m.1 : ℕ) : ℝ))) =
      ((m.1 : ℕ) : ℂ) ^ (-(((m.2 + 1 : ℕ) : ℂ) * θ.sigma + ((θ.tau : ℂ) + z))) := by
  have hp : ((m.1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast m.1.prop.ne_zero
  rw [ratio_eq_norm_mode_cpow, Complex.natCast_log (n := (m.1 : ℕ)),
    show -z * Complex.log ((m.1 : ℕ) : ℂ) = Complex.log ((m.1 : ℕ) : ℂ) * (-z) by ring,
    ← Complex.cpow_def_of_ne_zero hp, ← Complex.cpow_add _ _ hp]
  congr 1
  push_cast
  ring

theorem socleModeFactor_eq (z : ℂ) (m : AbelianZetaMode) :
    socleModeFactor θ z m =
      modeEulerFactor θ.sigma θ.tau m / modeEulerFactor θ.sigma ((θ.tau : ℂ) + z) m := by
  rw [socleModeFactor, ratio_mul_cexp, ratio_eq_norm_mode_cpow, modeEulerFactor,
    modeEulerFactor]

theorem ratio_mul_exp_lt_one {z : ℂ} (hz : 1 < θ.sigma + θ.tau + z.re) (m : AbelianZetaMode) :
    θ.toAbelianZetaParameters.ratio m * Real.exp (-z * Real.log (((m.1 : ℕ) : ℝ))).re < 1 := by
  have h := norm_mode_cpow_lt_one θ.sigma_pos (v := (θ.tau : ℂ) + z)
    (by simp only [Complex.add_re, Complex.ofReal_re]; linarith) m
  rw [← ratio_mul_cexp, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (θ.toAbelianZetaParameters.ratio_pos m)] at h
  exact h

/-- The socle moment generating function is the ratio of socle ladders, as an infinite product of
mode factors. -/
theorem hasProd_socleModeFactor {z : ℂ} (hz : 1 < θ.sigma + θ.tau + z.re) :
    HasProd (socleModeFactor θ z) (socleResponse θ.sigma θ.tau z) := by
  have h1 := hasProd_modeEulerFactor θ.sigma_pos (v := (θ.tau : ℂ))
    (by simpa using θ.firstDepth)
  have h2 := hasProd_modeEulerFactor θ.sigma_pos (v := (θ.tau : ℂ) + z)
    (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
  have hne : socleLadder θ.sigma ((θ.tau : ℂ) + z) ≠ 0 :=
    socleLadder_ne_zero_of_mem θ.sigma_pos (by
      simp only [socleChamber, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
      linarith)
  have h3 := h1.mul (hasProd_inv_of_ne_zero h2 (inv_ne_zero hne))
  simp only [inv_inv] at h3
  have hfun : socleModeFactor θ z = fun m => modeEulerFactor θ.sigma θ.tau m *
      (modeEulerFactor θ.sigma ((θ.tau : ℂ) + z) m)⁻¹ := by
    funext m
    rw [socleModeFactor_eq, div_eq_mul_inv]
  rw [hfun, socleResponse, div_eq_mul_inv, mul_comm]
  exact h3

theorem integral_gas_cexp_truncSocle (z : ℂ) (hz : 1 < θ.sigma + θ.tau + z.re) (N : ℕ) :
    ∫ k, Complex.exp (-z * truncSocle N k) ∂θ.gasMeasure =
      ∏ i ∈ Finset.range N, socleModeFactor θ z (modeAt i) := by
  set e := AbelianZetaParameters.modeEquivNat
  have h := integral_gasMeasure_cexp_finset θ.toAbelianZetaParameters
    (fun m => -z * Real.log (((m.1 : ℕ) : ℝ))) ((Finset.range N).map e.toEmbedding)
    (ratio_mul_exp_lt_one θ hz)
  rw [Finset.prod_map] at h
  have hfun : (fun k : AbelianZetaMode → ℕ => Complex.exp (-z * truncSocle N k)) =
      fun k => Complex.exp (∑ m ∈ (Finset.range N).map e.toEmbedding,
        (-z * Real.log (((m.1 : ℕ) : ℝ))) * k m) := by
    funext k
    congr 1
    rw [Finset.sum_map, truncSocle]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.coe_toEmbedding]
    ring
  rw [hfun, h]
  rfl

theorem tendsto_prod_socleModeFactor {z : ℂ} (hz : 1 < θ.sigma + θ.tau + z.re) :
    Tendsto (fun N => ∏ i ∈ Finset.range N, socleModeFactor θ z (modeAt i)) atTop
      (𝓝 (socleResponse θ.sigma θ.tau z)) :=
  ((AbelianZetaParameters.modeEquivNat.hasProd_iff).mpr
    (hasProd_socleModeFactor θ hz)).tendsto_prod_nat

theorem integrable_exp_truncSocle {u : ℝ} (hu : 1 < θ.sigma + θ.tau - u)
    (N : ℕ) : Integrable (fun k => Real.exp (u * truncSocle N k)) θ.gasMeasure := by
  set X : ℕ → (AbelianZetaMode → ℕ) → ℝ := fun i k =>
    (k (modeAt i) : ℝ) * Real.log (((modeAt i).1 : ℕ) : ℝ) with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i =>
    ((measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp
      (measurable_pi_apply (modeAt i))).mul_const _
  have hindep : iIndepFun X θ.gasMeasure := by
    have h := ((θ.toAbelianZetaParameters.iIndepFun_eval).precomp
      AbelianZetaParameters.modeEquivNat.injective).comp
      (fun i (n : ℕ) => (n : ℝ) * Real.log (((modeAt i).1 : ℕ) : ℝ))
      (fun i => measurable_from_top)
    exact h
  have hint : ∀ i ∈ Finset.range N, Integrable (fun k => Real.exp (u * X i k)) θ.gasMeasure := by
    intro i _
    have hz : 1 < θ.sigma + θ.tau + (-(u : ℂ)).re := by
      simp only [Complex.neg_re, Complex.ofReal_re]
      linarith
    have hmode := integrable_modeLaw_cexp θ.toAbelianZetaParameters (modeAt i)
      (-(-(u : ℂ)) * Real.log (((modeAt i).1 : ℕ) : ℝ)) (ratio_mul_exp_lt_one θ hz (modeAt i))
    have hreal : Integrable (fun n : ℕ => Real.exp (u * ((n : ℝ) *
        Real.log (((modeAt i).1 : ℕ) : ℝ)))) (θ.toAbelianZetaParameters.modeLaw (modeAt i)) := by
      refine hmode.norm.congr (Eventually.of_forall fun n => ?_)
      simp only
      rw [Complex.norm_exp]
      congr 1
      simp only [neg_neg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
      ring
    have hmap : θ.gasMeasure.map (fun k : AbelianZetaMode → ℕ => k (modeAt i)) =
        θ.toAbelianZetaParameters.modeLaw (modeAt i) := by
      rw [AbelianZetaParameters.gasMeasure]
      exact Measure.infinitePi_map_eval (μ := θ.toAbelianZetaParameters.modeLaw) (modeAt i)
    rw [← hmap] at hreal
    exact (integrable_map_measure
      (g := fun n : ℕ => Real.exp (u * ((n : ℝ) * Real.log (((modeAt i).1 : ℕ) : ℝ))))
      (f := fun k : AbelianZetaMode → ℕ => k (modeAt i))
      measurable_from_top.aestronglyMeasurable (measurable_pi_apply (modeAt i)).aemeasurable).mp
      hreal
  have h := hindep.integrable_exp_mul_sum (t := u) hXm hint
  refine h.congr (Eventually.of_forall fun k => ?_)
  simp only [Finset.sum_apply, hXdef, truncSocle]

/-- The real exponential moments of the truncated socle, computed by the mode product. -/
theorem integral_exp_truncSocle {u : ℝ} (hu : 1 < θ.sigma + θ.tau - u) (N : ℕ) :
    ∫ k, Real.exp (u * truncSocle N k) ∂θ.gasMeasure =
      ‖∏ i ∈ Finset.range N, socleModeFactor θ (-(u : ℂ)) (modeAt i)‖ := by
  have hz : 1 < θ.sigma + θ.tau + (-(u : ℂ)).re := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  rw [← integral_gas_cexp_truncSocle θ (-(u : ℂ)) hz N]
  have hfun : (fun k : AbelianZetaMode → ℕ => Complex.exp (-(-(u : ℂ)) * truncSocle N k)) =
      fun k => ((Real.exp (u * truncSocle N k) : ℝ) : ℂ) := by
    funext k
    rw [neg_neg, Complex.ofReal_exp]
    push_cast
    rfl
  rw [hfun, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)]

/-- **Real socle moments.**  `E exp(u Q) = ‖C_{σ,τ}(-u)‖` for `0 ≤ u < σ + τ - 1`. -/
theorem lintegral_gas_exp_socle {u : ℝ} (hu0 : 0 ≤ u) (hu : 1 < θ.sigma + θ.tau - u) :
    ∫⁻ k, ENNReal.ofReal (Real.exp (u * socleLog (classOf k))) ∂θ.gasMeasure =
      ENNReal.ofReal ‖socleResponse θ.sigma θ.tau (-(u : ℂ))‖ := by
  have hz : 1 < θ.sigma + θ.tau + (-(u : ℂ)).re := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  have hfin : ∀ᵐ k ∂θ.gasMeasure, (Function.support k).Finite :=
    ae_iff.mpr (gasMeasure_infiniteSupport_null θ)
  have hmono := lintegral_tendsto_of_tendsto_of_monotone (μ := θ.gasMeasure)
    (f := fun N k => ENNReal.ofReal (Real.exp (u * truncSocle N k)))
    (F := fun k => ENNReal.ofReal (Real.exp (u * socleLog (classOf k))))
    (fun N => (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_truncSocle N)))).aemeasurable)
    (Eventually.of_forall fun k a b hab => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (truncSocle_mono k hab) hu0)))
    (hfin.mono fun k hk => (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp ((tendsto_truncSocle hk).const_mul u)))
  have hvals : ∀ N, ∫⁻ k, ENNReal.ofReal (Real.exp (u * truncSocle N k)) ∂θ.gasMeasure =
      ENNReal.ofReal ‖∏ i ∈ Finset.range N, socleModeFactor θ (-(u : ℂ)) (modeAt i)‖ := by
    intro N
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_truncSocle θ hu N)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_truncSocle θ hu N]
  simp_rw [hvals] at hmono
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp
    ((continuous_norm.tendsto _).comp (tendsto_prod_socleModeFactor θ hz))
  exact tendsto_nhds_unique hmono hlim

theorem integrable_gas_exp_socle {u : ℝ} (hu0 : 0 ≤ u) (hu : 1 < θ.sigma + θ.tau - u) :
    Integrable (fun k => Real.exp (u * socleLog (classOf k))) θ.gasMeasure := by
  refine ⟨(Real.continuous_exp.measurable.comp (measurable_const.mul
    ((measurable_from_top (f := socleLog)).comp measurable_classOf))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    lintegral_gas_exp_socle θ hu0 hu]
  exact ENNReal.ofReal_lt_top

/-- `(AZC.12)` on the gas.  `E e^{-zQ} = C_{σ,τ}(z)` for `σ + τ + Re z > 1`. -/
theorem integral_gas_cexp_socle {z : ℂ} (hz : 1 < θ.sigma + θ.tau + z.re) :
    ∫ k, Complex.exp (-z * socleLog (classOf k)) ∂θ.gasMeasure =
      socleResponse θ.sigma θ.tau z := by
  set u := max 0 (-z.re) with hudef
  have hu0 : 0 ≤ u := le_max_left _ _
  have hu : 1 < θ.sigma + θ.tau - u := by
    rcases le_total 0 (-z.re) with h | h
    · rw [hudef, max_eq_right h]
      linarith
    · rw [hudef, max_eq_left h]
      linarith [θ.firstDepth]
  have hfin : ∀ᵐ k ∂θ.gasMeasure, (Function.support k).Finite :=
    ae_iff.mpr (gasMeasure_infiniteSupport_null θ)
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := θ.gasMeasure) (F := fun N k => Complex.exp (-z * truncSocle N k))
    (f := fun k => Complex.exp (-z * socleLog (classOf k)))
    (fun k => Real.exp (u * socleLog (classOf k)))
    (fun N => (Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_truncSocle N)))).aestronglyMeasurable)
    (integrable_gas_exp_socle θ hu0 hu)
    (fun N => hfin.mono fun k hk => by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have h1 := truncSocle_le_socleLog hk N
      have h2 := truncSocle_nonneg N k
      have h3 : -z.re ≤ u := le_max_right _ _
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
        Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith)
    (hfin.mono fun k hk => (Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp (tendsto_truncSocle hk)).const_mul (-z)))
  have hvals : ∀ N, ∫ k, Complex.exp (-z * truncSocle N k) ∂θ.gasMeasure =
      ∏ i ∈ Finset.range N, socleModeFactor θ z (modeAt i) :=
    integral_gas_cexp_truncSocle θ z hz
  simp_rw [hvals] at hdom
  exact tendsto_nhds_unique hdom (tendsto_prod_socleModeFactor θ hz)

end Gas

/-! ## The class law -/

section ClassLaw

variable (θ : AbelianZetaConvergentParameters)

/-- `(AZC.12)`  **Socle moment generating function.**  Under the zeta-Gibbs law,
`E e^{-zQ} = ∏_{j≥1} ζ(jσ + τ + z)/ζ(jσ + τ)` whenever `σ + τ + Re z > 1`. -/
theorem integral_classLaw_cexp_socle {z : ℂ} (hz : 1 < θ.sigma + θ.tau + z.re) :
    ∫ A, Complex.exp (-z * socleLog A) ∂classLaw θ.toAbelianZetaParameters =
      socleResponse θ.sigma θ.tau z := by
  rw [classLaw_eq_map, integral_map measurable_classOf.aemeasurable
    measurable_from_top.aestronglyMeasurable]
  exact integral_gas_cexp_socle θ hz

/-- Every exponential moment `E exp(u Q)` with `u < σ + τ - 1` is finite. -/
theorem integrable_classLaw_exp_socle {u : ℝ} (hu : 1 < θ.sigma + θ.tau - u) :
    Integrable (fun A => Real.exp (u * socleLog A)) (classLaw θ.toAbelianZetaParameters) := by
  rcases le_total 0 u with hu0 | hu0
  · rw [classLaw_eq_map, integrable_map_measure measurable_from_top.aestronglyMeasurable
      measurable_classOf.aemeasurable]
    exact integrable_gas_exp_socle θ hu0 hu
  · refine (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable
      (Eventually.of_forall fun A => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hu0 (socleLog_nonneg A))

end ClassLaw

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
