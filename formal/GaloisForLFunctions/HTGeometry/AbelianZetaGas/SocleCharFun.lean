import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Core
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DefectLadder

/-!
# Characteristic functions of the gas occupation observables

Each mode of the gas carries an independent geometric occupation law, so the characteristic
function of a linear observable `∑_m a_m N_m` over a finite set of modes is the corresponding
finite product of geometric characteristic functions `(1 − q_m)/(1 − q_m e^{i a_m})`.

This is the analytic bridge between the corpus's `gasMeasure` and the `q`-Pochhammer objects: the
depth modes of a single prime produce exactly the factors of `(q^{1+it}; q)_∞`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace AbelianZetaParameters

/-- The characteristic function of one geometric mode. -/
theorem integral_modeLaw_expo (θ : AbelianZetaParameters) (m : AbelianZetaMode) (a : ℝ) :
    ∫ n : ℕ, Complex.exp ((a * n : ℝ) * Complex.I) ∂(θ.modeLaw m)
      = (1 - (θ.ratio m : ℂ)) / (1 - (θ.ratio m : ℂ) * Complex.exp ((a : ℝ) * Complex.I)) := by
  classical
  have hq0 : (0 : ℝ) < θ.ratio m := θ.ratio_pos m
  have hq1 : θ.ratio m < 1 := θ.ratio_lt_one m
  have hsucc : ((θ.success m : ℝ)) = 1 - θ.ratio m := by
    have := θ.one_sub_success m; linarith
  have hz : ‖Complex.exp ((a : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hnorm : ‖(θ.ratio m : ℂ) * Complex.exp ((a : ℝ) * Complex.I)‖ < 1 := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1
  rw [modeLaw, integral_geometricMeasure (θ.success_ne_zero m)]
  have hterm : ∀ n : ℕ,
      ((1 - (θ.success m : ℝ)) ^ n * (θ.success m : ℝ)) •
          Complex.exp ((a * n : ℝ) * Complex.I)
        = (1 - (θ.ratio m : ℂ)) * ((θ.ratio m : ℂ) * Complex.exp ((a : ℝ) * Complex.I)) ^ n := by
    intro n
    have hexp : Complex.exp ((a * n : ℝ) * Complex.I)
        = Complex.exp ((a : ℝ) * Complex.I) ^ n := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp, hsucc, Complex.real_smul]
    push_cast
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
  rw [div_eq_mul_inv]

/-- The coordinates of the gas measure are independent. -/
theorem iIndepFun_eval (θ : AbelianZetaParameters) :
    iIndepFun (fun (m : AbelianZetaMode) (k : AbelianZetaMode → ℕ) => k m) θ.gasMeasure := by
  rw [gasMeasure]
  exact iIndepFun_infinitePi (X := fun _ : AbelianZetaMode => (id : ℕ → ℕ))
    (fun _ => measurable_id)

theorem integral_gasMeasure_eval (θ : AbelianZetaParameters) (m : AbelianZetaMode)
    (f : ℕ → ℂ) :
    ∫ k, f (k m) ∂θ.gasMeasure = ∫ n, f n ∂(θ.modeLaw m) := by
  have hmap : θ.gasMeasure.map (fun k : AbelianZetaMode → ℕ => k m) = θ.modeLaw m := by
    rw [gasMeasure]
    exact MeasureTheory.Measure.infinitePi_map_eval (μ := θ.modeLaw) m
  rw [← hmap, integral_map (measurable_pi_apply m).aemeasurable
    (Measurable.aestronglyMeasurable (measurable_from_top))]

/-- **The characteristic function of a finite-mode linear observable** is the product of the
geometric characteristic functions of its modes. -/
theorem integral_gasMeasure_expo_finset (θ : AbelianZetaParameters)
    (a : AbelianZetaMode → ℝ) (s : Finset AbelianZetaMode) :
    ∫ k, Complex.exp ((∑ m ∈ s, a m * k m : ℝ) * Complex.I) ∂θ.gasMeasure
      = ∏ m ∈ s, (1 - (θ.ratio m : ℂ))
          / (1 - (θ.ratio m : ℂ) * Complex.exp ((a m : ℝ) * Complex.I)) := by
  classical
  have hindep : iIndepFun (fun (m : s) (k : AbelianZetaMode → ℕ) => k (m : AbelianZetaMode))
      θ.gasMeasure := (θ.iIndepFun_eval).precomp Subtype.coe_injective
  have hsplit : ∀ k : AbelianZetaMode → ℕ,
      Complex.exp ((∑ m ∈ s, a m * k m : ℝ) * Complex.I)
        = ∏ m : s, Complex.exp ((a (m : AbelianZetaMode) * k (m : AbelianZetaMode) : ℝ)
            * Complex.I) := by
    intro k
    rw [show (((∑ m ∈ s, a m * k m : ℝ) : ℂ)) * Complex.I
        = ∑ m ∈ s, ((a m * k m : ℝ) : ℂ) * Complex.I by
      push_cast
      rw [Finset.sum_mul], Complex.exp_sum,
      ← Finset.prod_coe_sort s (fun m => Complex.exp ((a m * k m : ℝ) * Complex.I))]
  simp only [hsplit]
  rw [hindep.integral_fun_prod_comp
    (f := fun (m : s) (n : ℕ) => Complex.exp ((a (m : AbelianZetaMode) * n : ℝ) * Complex.I))
    (fun _ => (measurable_pi_apply _).aemeasurable)
    (fun _ => (measurable_from_top).aestronglyMeasurable)]
  rw [← Finset.prod_coe_sort s (fun m => (1 - (θ.ratio m : ℂ))
    / (1 - (θ.ratio m : ℂ) * Complex.exp ((a m : ℝ) * Complex.I)))]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [θ.integral_gasMeasure_eval (m : AbelianZetaMode)
    (fun n => Complex.exp ((a (m : AbelianZetaMode) * n : ℝ) * Complex.I)),
    θ.integral_modeLaw_expo]

end AbelianZetaParameters

/-! ## The depth modes of one prime multiply to Jackson's `q`-Gamma -/

/-- The geometric characteristic functions of the depth modes of a nome have a product, namely
`(q;q)_∞` divided by the phase-twisted product `(q e^{−iθ}; q)_∞`. -/
theorem hasProd_modeCharFun (q : RealEulerNome) (θ : ℝ) :
    HasProd (fun j : ℕ => ((1 - q.val ^ (j + 1) : ℝ) : ℂ)
        / (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ))
      (((realQFactorialInf q : ℝ) : ℂ) / defectProduct q θ) := by
  have hnum : HasProd (fun j : ℕ => ((1 - q.val ^ (j + 1) : ℝ) : ℂ))
      ((realQFactorialInf q : ℝ) : ℂ) := by
    have hreal : HasProd (fun j : ℕ => (1 - q.val ^ (j + 1))) (realQFactorialInf q) :=
      (realQFactorial_multipliable q).hasProd
    exact hreal.map (Complex.ofRealHom : ℝ →+* ℂ) Complex.continuous_ofReal
  have hden : HasProd (fun j : ℕ => 1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ)
      (defectProduct q θ) := (multipliable_defectFactor q θ).hasProd
  have hne : defectProduct q θ ≠ 0 := defectProduct_ne_zero q θ
  have hdiv : Filter.Tendsto (fun s : Finset ℕ =>
      (∏ b ∈ s, ((1 - q.val ^ (b + 1) : ℝ) : ℂ))
        / (∏ b ∈ s, (1 - ((q.val ^ (b + 1) : ℝ) : ℂ) * modePhase θ)))
      (SummationFilter.unconditional ℕ).filter
      (𝓝 (((realQFactorialInf q : ℝ) : ℂ) / defectProduct q θ)) :=
    Filter.Tendsto.div hnum hden hne
  exact hdiv.congr fun s => (Finset.prod_div_distrib _ _).symm

/-- The `q`-Gamma value `Γ_q(1+it)` is the centered characteristic function of the total
occupation of a nome: the prefactor is the centering `e^{-it log(1-q)}` and the product is the
one over depth modes. -/
theorem qGammaOn_eq_centered_tprod (q : RealEulerNome) (t : ℝ) :
    qGammaOn q (1 + (t : ℂ) * Complex.I)
      = Complex.exp ((-(t * Real.log (1 - q.val)) : ℝ) * Complex.I)
        * ∏' j : ℕ, (((1 - q.val ^ (j + 1) : ℝ) : ℂ)
            / (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t))) := by
  have hbase : (0 : ℝ) < 1 - q.val := by have := q.lt_one; linarith
  have hprefactor : ((1 - q.val : ℝ) : ℂ) ^ (1 - (1 + (t : ℂ) * Complex.I))
      = Complex.exp ((-(t * Real.log (1 - q.val)) : ℝ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hbase.ne'), ← Complex.ofReal_log hbase.le]
    congr 1
    push_cast
    ring
  rw [qGammaOn, hprefactor, (hasProd_modeCharFun q (phaseAngle q t)).tprod_eq,
    qDenomProduct_eq_defectProduct]

/-! ## The socle observable of one prime -/

/-- At zero chemical potential the mode ratios of a prime are the powers of its nome. -/
theorem ratio_temperatureParameters {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) (j : ℕ) :
    (AbelianZetaParameters.temperatureParameters σ hσ).ratio (p, j) = (primeNome hσ p).val ^ (j + 1) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hexp : (AbelianZetaParameters.temperatureParameters σ hσ).exponent (p, j)
      = ((j : ℝ) + 1) * σ := by
    simp [AbelianZetaParameters.exponent, AbelianZetaParameters.temperatureParameters,
      AbelianZetaMode.depth]
  have hr : (AbelianZetaParameters.temperatureParameters σ hσ).ratio (p, j)
      = ((p : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * σ)) := by
    rw [AbelianZetaParameters.ratio, hexp]
  rw [hr, primeNome_val, ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-σ)) (j + 1),
    ← Real.rpow_mul hp.le]
  congr 1
  push_cast
  ring

/-- The phase of one unit of occupation of a mode of `p`. -/
noncomputable def socleCoeff (σ t : ℝ) (p : Nat.Primes) : ℝ := -(t * (σ * Real.log ((p : ℕ) : ℝ)))

theorem exp_socleCoeff {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) (t : ℝ) :
    Complex.exp ((socleCoeff σ t p : ℝ) * Complex.I)
      = modePhase (phaseAngle (primeNome hσ p) t) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [modePhase, socleCoeff, phaseAngle, primeNome_val, Real.log_rpow hp]
  congr 2
  push_cast
  ring

/-- **The characteristic function of the socle observable of one prime is `Γ_{q_p}(1+it)`.**
The observable is `ξ_p = −σ log p · N_p − log(1−q_p)`, with `N_p` the total occupation of the
depth modes of `p`; truncating at depth `J` and letting `J → ∞` produces Jackson's `q`-Gamma. -/
theorem tendsto_charFun_socle {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) (t : ℝ) :
    Filter.Tendsto (fun J : ℕ =>
        Complex.exp ((-(t * Real.log (1 - (primeNome hσ p).val)) : ℝ) * Complex.I)
          * ∫ k, Complex.exp ((∑ m ∈ (Finset.range J).image (fun j => ((p, j) : AbelianZetaMode)),
                socleCoeff σ t p * k m : ℝ) * Complex.I)
              ∂(AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure)
      Filter.atTop (𝓝 (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I))) := by
  classical
  set q := primeNome hσ p with hq
  have hinj : Function.Injective (fun j : ℕ => ((p, j) : AbelianZetaMode)) := by
    intro i j hij
    exact (Prod.mk.injEq _ _ _ _ ▸ hij).2
  have hfactor : ∀ J : ℕ,
      ∫ k, Complex.exp ((∑ m ∈ (Finset.range J).image (fun j => ((p, j) : AbelianZetaMode)),
            socleCoeff σ t p * k m : ℝ) * Complex.I)
          ∂(AbelianZetaParameters.temperatureParameters σ hσ).gasMeasure
        = ∏ j ∈ Finset.range J, (((1 - q.val ^ (j + 1) : ℝ) : ℂ)
            / (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t))) := by
    intro J
    rw [AbelianZetaParameters.integral_gasMeasure_expo_finset,
      Finset.prod_image fun i _ j _ h => hinj h]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ratio_temperatureParameters hσ p j, exp_socleCoeff hσ p t, hq]
    push_cast
    ring
  simp only [hfactor]
  have hprod := (hasProd_modeCharFun q (phaseAngle q t)).tendsto_prod_nat
  have hlim := hprod.const_mul
    (Complex.exp ((-(t * Real.log (1 - q.val)) : ℝ) * Complex.I))
  have hval : qGammaOn q (1 + (t : ℂ) * Complex.I)
      = Complex.exp ((-(t * Real.log (1 - q.val)) : ℝ) * Complex.I)
        * (((realQFactorialInf q : ℝ) : ℂ) / defectProduct q (phaseAngle q t)) := by
    rw [qGammaOn_eq_centered_tprod q t, (hasProd_modeCharFun q (phaseAngle q t)).tprod_eq]
  rw [hval]
  exact hlim

end GaloisForLFunctions.HTGeometry
