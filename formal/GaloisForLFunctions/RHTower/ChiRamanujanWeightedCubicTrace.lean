import GaloisForLFunctions.RHTower.ChiRamanujanWeightedCubicLocal
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import GaloisForLFunctions.HTGeometry.MultivariableVitali
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
/-!
# Complete weighted cubic trace and critical Euler correction

For every damping parameter with real part greater than one and every pair
of imaginary Mellin frequencies, the full signed valuation sum over each
finite prime set tends to the exact six-zeta expression. No signed sector,
frequency range or prime is discarded.

The mixed Euler correction converges locally uniformly and is jointly
holomorphic on a complex tube crossing the critical plane. Its values on
both frequency axes are exactly one. The multivariable Weierstrass theorem
is supplied by the existing corpus, not assumed.

Critical distributional limits, physical near-resonances and the coupled
height/damping limit are separate obligations; this is not an RH theorem.
-/

noncomputable section
open scoped BigOperators Topology
namespace RHTower.BAGTrace

def cubicPrimeBase (p : Nat.Primes) (s : ℂ) : ℂ := (p : ℂ)^(-s)

def cubicPrimeFactor (p : Nat.Primes) (σ α β : ℂ) : ℂ :=
  cubicRegularFactor (cubicPrimeBase p σ) (cubicPrimeBase p α) (cubicPrimeBase p β)

def cubicEulerCorrection (σ α β : ℂ) : ℂ := ∏' p, cubicPrimeFactor p σ α β

def cubicTube : Set (ℂ × ℂ × ℂ) :=
  {w | 7/8 < w.1.re ∧ |w.2.1.re| < 1/16 ∧ |w.2.2.re| < 1/16}

def cubicMajorant : ℝ := 32/(1-(2 : ℝ)^(-(3/4) : ℝ))^4

theorem cubicPrimeBase_ne_zero (p : Nat.Primes) (s : ℂ) : cubicPrimeBase p s ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast p.property.ne_zero))

theorem norm_cubicPrimeBase (p : Nat.Primes) (s : ℂ) :
    ‖cubicPrimeBase p s‖ = (p : ℝ)^(-s.re) := by
  simp only [cubicPrimeBase, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]

theorem cubicPrimeBase_inv (p : Nat.Primes) (s : ℂ) :
    (cubicPrimeBase p s)⁻¹ = cubicPrimeBase p (-s) := by
  simp only [cubicPrimeBase, neg_neg, Complex.cpow_neg, inv_inv]

theorem cubicPrimeBase_mul (p : Nat.Primes) (s t : ℂ) :
    cubicPrimeBase p s * cubicPrimeBase p t = cubicPrimeBase p (s+t) := by
  simp only [cubicPrimeBase, neg_add]
  exact (Complex.cpow_add _ _ (by exact_mod_cast p.property.ne_zero)).symm

theorem cubicPrimeBase_div (p : Nat.Primes) (s t : ℂ) :
    cubicPrimeBase p s / cubicPrimeBase p t = cubicPrimeBase p (s-t) := by
  rw [div_eq_mul_inv, cubicPrimeBase_inv, cubicPrimeBase_mul, sub_eq_add_neg]

theorem norm_cubicPrimeBase_le {p : Nat.Primes} {s : ℂ} {a : ℝ} (h : a ≤ s.re) :
    ‖cubicPrimeBase p s‖ ≤ (p : ℝ)^(-a) := by
  rw [norm_cubicPrimeBase]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast p.property.one_lt.le) (neg_le_neg h)

private theorem prime_rpow_le (p : Nat.Primes) :
    (p : ℝ)^(-(3/4) : ℝ) ≤ (2 : ℝ)^(-(3/4) : ℝ) :=
  Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.property.two_le) (by norm_num)

private theorem cubic_c_lt : (2 : ℝ)^(-(3/4) : ℝ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem norm_cubicPrimeFactor_sub_one_le (p : Nat.Primes) {σ α β : ℂ}
    (hσ : 7/8 ≤ σ.re) (hα : |α.re| ≤ 1/16) (hβ : |β.re| ≤ 1/16) :
    ‖cubicPrimeFactor p σ α β-1‖ ≤ cubicMajorant * (p : ℝ)^(-(3/2) : ℝ) := by
  let a : ℝ := (p : ℝ)^(-(7/8) : ℝ)
  let r : ℝ := (p : ℝ)^((1/16) : ℝ)
  let c : ℝ := (2 : ℝ)^(-(3/4) : ℝ)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  have hr : 1 ≤ r := Real.one_le_rpow hp1 (by norm_num)
  have hzc : ‖cubicPrimeBase p σ‖ ≤ c :=
    (norm_cubicPrimeBase_le (by linarith : (3/4 : ℝ) ≤ σ.re)).trans (prime_rpow_le p)
  have hz : ‖cubicPrimeBase p σ‖ ≤ a := norm_cubicPrimeBase_le hσ
  have hU : ‖cubicPrimeBase p α‖ ≤ r := by
    simpa only [neg_neg] using norm_cubicPrimeBase_le (neg_le_of_abs_le hα)
  have hV : ‖cubicPrimeBase p β‖ ≤ r := by
    simpa only [neg_neg] using norm_cubicPrimeBase_le (neg_le_of_abs_le hβ)
  have hUi : ‖(cubicPrimeBase p α)⁻¹‖ ≤ r := by
    rw [cubicPrimeBase_inv]
    simpa only [neg_neg] using norm_cubicPrimeBase_le (p := p) (s := -α)
      (a := -(1/16)) (by simpa only [Complex.neg_re, neg_le_neg_iff] using le_of_abs_le hα)
  have hVi : ‖(cubicPrimeBase p β)⁻¹‖ ≤ r := by
    rw [cubicPrimeBase_inv]
    simpa only [neg_neg] using norm_cubicPrimeBase_le (p := p) (s := -β)
      (a := -(1/16)) (by simpa only [Complex.neg_re, neg_le_neg_iff] using le_of_abs_le hβ)
  have hUV : ‖cubicPrimeBase p σ*(cubicPrimeBase p α/cubicPrimeBase p β)‖ ≤ c := by
    rw [cubicPrimeBase_div, cubicPrimeBase_mul]
    apply (norm_cubicPrimeBase_le (a := 3/4) ?_).trans (prime_rpow_le p)
    simp only [Complex.add_re, Complex.sub_re]
    have := neg_le_of_abs_le hα
    have := le_of_abs_le hβ
    linarith
  have hVU : ‖cubicPrimeBase p σ*(cubicPrimeBase p β/cubicPrimeBase p α)‖ ≤ c := by
    rw [cubicPrimeBase_div, cubicPrimeBase_mul]
    apply (norm_cubicPrimeBase_le (a := 3/4) ?_).trans (prime_rpow_le p)
    simp only [Complex.add_re, Complex.sub_re]
    have := neg_le_of_abs_le hβ
    have := le_of_abs_le hα
    linarith
  have h := norm_cubicRegularFactor_sub_one_le hr cubic_c_lt hz hzc hU hV hUi hVi hUV hVU
  refine h.trans_eq ?_
  have hpow : a^2*r^4 = (p : ℝ)^(-(3/2) : ℝ) := by
    dsimp [a,r]
    rw [← Real.rpow_mul_natCast hp0.le, ← Real.rpow_mul_natCast hp0.le,
      ← Real.rpow_add hp0]
    congr 1
    norm_num
  dsimp [cubicMajorant, c]
  rw [← hpow]
  ring

theorem isOpen_cubicTube : IsOpen cubicTube :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
    ((isOpen_lt ((Complex.continuous_re.comp (continuous_fst.comp continuous_snd)).abs)
      continuous_const).inter
      (isOpen_lt ((Complex.continuous_re.comp (continuous_snd.comp continuous_snd)).abs)
        continuous_const))

theorem one_sub_cubicPrimeBase_ne_zero (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    1-cubicPrimeBase p s ≠ 0 := by
  have h : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hs)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at h
  exact lt_irrefl _ h

private theorem cubicTube_cross_pos {w : ℂ × ℂ × ℂ} (hw : w ∈ cubicTube) :
    0 < (w.1+(w.2.1-w.2.2)).re ∧ 0 < (w.1+(w.2.2-w.2.1)).re := by
  have ha := abs_lt.mp hw.2.1
  have hb := abs_lt.mp hw.2.2
  have hs := hw.1
  simp only [Complex.add_re, Complex.sub_re]
  constructor <;> linarith

theorem differentiableOn_cubicPrimeFactor (p : Nat.Primes) :
    DifferentiableOn ℂ (fun w : ℂ × ℂ × ℂ => cubicPrimeFactor p w.1 w.2.1 w.2.2)
      cubicTube := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hz : Differentiable ℂ (fun w : ℂ × ℂ × ℂ => cubicPrimeBase p w.1) :=
    differentiable_fst.neg.const_cpow (.inl hp0)
  have hu : Differentiable ℂ (fun w : ℂ × ℂ × ℂ => cubicPrimeBase p w.2.1) :=
    (differentiable_fst.comp differentiable_snd).neg.const_cpow (.inl hp0)
  have hv : Differentiable ℂ (fun w : ℂ × ℂ × ℂ => cubicPrimeBase p w.2.2) :=
    (differentiable_snd.comp differentiable_snd).neg.const_cpow (.inl hp0)
  have hui := hu.differentiableOn.inv (S := cubicTube) (fun w _ => cubicPrimeBase_ne_zero p w.2.1)
  have hvi := hv.differentiableOn.inv (S := cubicTube) (fun w _ => cubicPrimeBase_ne_zero p w.2.2)
  have hUV := hu.differentiableOn.mul hvi
  have hVU := hv.differentiableOn.mul hui
  have hn := ((((((hu.differentiableOn.add hv.differentiableOn).sub
    (differentiableOn_const 1)).sub (hz.differentiableOn.pow 2)).sub hUV).sub hVU).add
    (hz.differentiableOn.mul hui)).add (hz.differentiableOn.mul hvi)
  have hz1 := (differentiableOn_const (s := cubicTube) 1).sub hz.differentiableOn
  have hd2 := (differentiableOn_const 1).sub (hz.differentiableOn.mul hVU)
  have hd3 := (differentiableOn_const 1).sub (hz.differentiableOn.mul hUV)
  have hd : ∀ w ∈ cubicTube,
      (1-cubicPrimeBase p w.1)^2 *
        (1-cubicPrimeBase p w.1*(cubicPrimeBase p w.2.2/cubicPrimeBase p w.2.1)) *
        (1-cubicPrimeBase p w.1*(cubicPrimeBase p w.2.1/cubicPrimeBase p w.2.2)) ≠ 0 := by
    intro w hw
    rw [cubicPrimeBase_div, cubicPrimeBase_div, cubicPrimeBase_mul, cubicPrimeBase_mul]
    have hpos : 0 < w.1.re := lt_trans (by norm_num) hw.1
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (one_sub_cubicPrimeBase_ne_zero p hpos))
      (one_sub_cubicPrimeBase_ne_zero p (cubicTube_cross_pos hw).2))
      (one_sub_cubicPrimeBase_ne_zero p (cubicTube_cross_pos hw).1)
  convert (differentiableOn_const 1).add
      (((((hz.differentiableOn.pow 2).mul ((differentiableOn_const 1).sub hui)).mul
        ((differentiableOn_const 1).sub hvi)).mul hn).mul
        ((((hz1.pow 2).mul hd2).mul hd3).inv (by
          intro w hw
          simpa only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply, div_eq_mul_inv]
            using hd w hw))) using 1 <;> try rfl

theorem hasProdLocallyUniformlyOn_cubicPrimeFactor :
    HasProdLocallyUniformlyOn
      (fun p : Nat.Primes => fun w : ℂ × ℂ × ℂ => cubicPrimeFactor p w.1 w.2.1 w.2.2)
      (fun w => cubicEulerCorrection w.1 w.2.1 w.2.2) cubicTube := by
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ)^(-(3/2) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2) : ℝ) < -1)).subtype Nat.Prime
  have h := Summable.hasProdLocallyUniformlyOn_one_add isOpen_cubicTube
    (hpow.mul_left cubicMajorant)
    (f := fun p : Nat.Primes => fun w : ℂ × ℂ × ℂ => cubicPrimeFactor p w.1 w.2.1 w.2.2-1)
    (.of_forall (fun p w hw => norm_cubicPrimeFactor_sub_one_le p
      hw.1.le hw.2.1.le hw.2.2.le))
    (fun p => (differentiableOn_cubicPrimeFactor p).continuousOn.sub continuousOn_const)
  simpa only [add_sub_cancel, cubicEulerCorrection] using h

theorem continuousOn_cubicEulerCorrection :
    ContinuousOn (fun w : ℂ × ℂ × ℂ => cubicEulerCorrection w.1 w.2.1 w.2.2) cubicTube := by
  apply hasProdLocallyUniformlyOn_cubicPrimeFactor.continuousOn
  exact Filter.Eventually.frequently (.of_forall fun t => by
    simpa only [Finset.prod_fn] using continuousOn_finsetProd t
      (fun p _ => (differentiableOn_cubicPrimeFactor p).continuousOn))

theorem cubicEulerCorrection_zero_left (σ β : ℂ) : cubicEulerCorrection σ 0 β = 1 := by
  simp [cubicEulerCorrection, cubicPrimeFactor, cubicPrimeBase, cubicRegularFactor]

theorem cubicEulerCorrection_zero_right (σ α : ℂ) : cubicEulerCorrection σ α 0 = 1 := by
  simp [cubicEulerCorrection, cubicPrimeFactor, cubicPrimeBase, cubicRegularFactor]

theorem weightedEuler_eq_regularFactor {z U V : ℂ}
    (hU : U ≠ 0) (hV : V ≠ 0) (hz : 1-z ≠ 0)
    (hx : 1-z*U ≠ 0) (hy : 1-z*V ≠ 0)
    (hxi : 1-z/U ≠ 0) (hyi : 1-z/V ≠ 0)
    (huv : 1-z*(U/V) ≠ 0) (hvu : 1-z*(V/U) ≠ 0) :
    weightedEuler z (z*U) (z*V) = cubicRegularFactor z U V *
      ((1-z*(V/U))*(1-z*(U/V))) /
        ((1-z*U)*(1-z*V)*(1-z/U)*(1-z/V)) := by
  have h := cubicCorrection_mixed_factor hU hV hz hx hy huv hvu
  change cubicCorrection z U V = cubicRegularFactor z U V at h
  unfold cubicCorrection at h
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hx hy) hxi) hyi)).mpr
  have h' := (div_eq_iff (mul_ne_zero hvu huv)).mp h
  simpa only [mul_assoc] using h'

def weightedTrace (σ α β : ℂ) (P : Finset Nat.Primes) : ℂ :=
  ∑' v : P → ℤ × ℤ, ∏ p : P,
    weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)) (v p)

theorem weightedTrace_eq {σ α β : ℂ} (hα : 0 < (σ+α).re) (hβ : 0 < (σ+β).re)
    (P : Finset Nat.Primes) : weightedTrace σ α β P =
      ∏ p ∈ P, weightedEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
        (cubicPrimeBase p (σ+β)) := by
  have hn (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hs)
  exact (complex_finite_product_hasSum P
    (fun p => weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)))
    (fun p => weightedEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)))
    (fun p => weightedLocal_hasSum _ (hn _ _ hα) (hn _ _ hβ))).tsum_eq.trans
      (Finset.prod_coe_sort P (fun p => weightedEuler (cubicPrimeBase p σ)
        (cubicPrimeBase p (σ+α)) (cubicPrimeBase p (σ+β))))

private theorem zeta_denominator_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1-cubicPrimeBase p s) (riemannZeta s)⁻¹ := by
  have h := Filter.Tendsto.inv₀ (riemannZeta_eulerProduct_hasProd hs)
    (riemannZeta_ne_zero_of_one_le_re hs.le)
  simpa only [HasProd, SummationFilter.unconditional, ← Finset.prod_inv_distrib,
    inv_inv, cubicPrimeBase] using h

private theorem weightedEuler_prime_eq (p : Nat.Primes) {σ α β : ℂ}
    (hσ : 1 < σ.re) (hα : α.re = 0) (hβ : β.re = 0) :
    weightedEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)) =
    cubicPrimeFactor p σ α β * (1-cubicPrimeBase p (σ+(β-α))) *
      (1-cubicPrimeBase p (σ+(α-β))) * (1-cubicPrimeBase p (σ+α))⁻¹ *
      (1-cubicPrimeBase p (σ+β))⁻¹ * (1-cubicPrimeBase p (σ-α))⁻¹ *
      (1-cubicPrimeBase p (σ-β))⁻¹ := by
  have hpos : 0 < σ.re := lt_trans zero_lt_one hσ
  have hn (s : ℂ) (hs : s.re = σ.re) : 1-cubicPrimeBase p s ≠ 0 :=
    one_sub_cubicPrimeBase_ne_zero p (hs ▸ hpos)
  have hx : 1-cubicPrimeBase p σ*cubicPrimeBase p α ≠ 0 := by
    rw [cubicPrimeBase_mul]
    exact hn _ (by simp [hα])
  have hy : 1-cubicPrimeBase p σ*cubicPrimeBase p β ≠ 0 := by
    rw [cubicPrimeBase_mul]
    exact hn _ (by simp [hβ])
  have hxi : 1-cubicPrimeBase p σ/cubicPrimeBase p α ≠ 0 := by
    rw [cubicPrimeBase_div]
    exact hn _ (by simp [hα])
  have hyi : 1-cubicPrimeBase p σ/cubicPrimeBase p β ≠ 0 := by
    rw [cubicPrimeBase_div]
    exact hn _ (by simp [hβ])
  have huv : 1-cubicPrimeBase p σ*(cubicPrimeBase p α/cubicPrimeBase p β) ≠ 0 := by
    rw [cubicPrimeBase_div, cubicPrimeBase_mul]
    exact hn _ (by simp [hα,hβ])
  have hvu : 1-cubicPrimeBase p σ*(cubicPrimeBase p β/cubicPrimeBase p α) ≠ 0 := by
    rw [cubicPrimeBase_div, cubicPrimeBase_mul]
    exact hn _ (by simp [hα,hβ])
  have h := weightedEuler_eq_regularFactor (cubicPrimeBase_ne_zero p α)
    (cubicPrimeBase_ne_zero p β) (hn _ rfl) hx hy hxi hyi huv hvu
  simp only [cubicPrimeBase_div, cubicPrimeBase_mul] at h
  rw [h]
  simp only [cubicPrimeFactor, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Full weighted signed trace, with no omitted valuation sectors or finite-prime cutoff.
The correction is normally convergent on a complex neighborhood of the critical plane. -/
theorem complete_weighted_trace_six_zeta {σ α β : ℂ}
    (hσ : 1 < σ.re) (hα : α.re = 0) (hβ : β.re = 0) :
    Filter.Tendsto (weightedTrace σ α β) Filter.atTop
      (𝓝 (cubicEulerCorrection σ α β *
        ((riemannZeta (σ+(β-α)))⁻¹ * (riemannZeta (σ+(α-β)))⁻¹) *
        riemannZeta (σ+α) * riemannZeta (σ+β) *
        riemannZeta (σ-α) * riemannZeta (σ-β))) := by
  have hmem : (σ,α,β) ∈ cubicTube := by
    refine ⟨by linarith, ?_, ?_⟩ <;> simp [hα, hβ]
  have hz (s : ℂ) (hs : s.re = σ.re) :
      HasProd (fun p : Nat.Primes => (1-cubicPrimeBase p s)⁻¹) (riemannZeta s) :=
    riemannZeta_eulerProduct_hasProd (hs ▸ hσ)
  have h0 := (hasProdLocallyUniformlyOn_cubicPrimeFactor.hasProd hmem).mul
    (zeta_denominator_hasProd (s := σ+(β-α)) (by simpa [hα,hβ] using hσ))
  have h1 := h0.mul
    (zeta_denominator_hasProd (s := σ+(α-β)) (by simpa [hα,hβ] using hσ))
  have h2 := (h1.mul (hz (σ+α) (by simp [hα]))).mul (hz (σ+β) (by simp [hβ]))
  have h := (h2.mul (hz (σ-α) (by simp [hα]))).mul (hz (σ-β) (by simp [hβ]))
  have h' := h.congr_fun (fun p => weightedEuler_prime_eq p hσ hα hβ)
  have ha : 0 < (σ+α).re := by simp only [Complex.add_re, hα, add_zero]; linarith
  have hb : 0 < (σ+β).re := by simp only [Complex.add_re, hβ, add_zero]; linarith
  change Filter.Tendsto (fun P => weightedTrace σ α β P) _ _
  simpa only [HasProd, SummationFilter.unconditional, weightedTrace_eq ha hb, mul_assoc] using h'

def cubicCoordinateTube : Set (Fin 3 → ℂ) := {w | (w 0,w 1,w 2) ∈ cubicTube}

theorem isOpen_cubicCoordinateTube : IsOpen cubicCoordinateTube :=
  isOpen_cubicTube.preimage ((continuous_apply 0).prodMk
    ((continuous_apply 1).prodMk (continuous_apply 2)))

private theorem differentiableOn_cubicCoordinatePrimeFactor (p : Nat.Primes) :
    DifferentiableOn ℂ (fun w : Fin 3 → ℂ => cubicPrimeFactor p (w 0) (w 1) (w 2))
      cubicCoordinateTube := by
  have he : Differentiable ℂ (fun w : Fin 3 → ℂ => (w 0,w 1,w 2)) :=
    (differentiable_apply 0).prodMk ((differentiable_apply 1).prodMk (differentiable_apply 2))
  exact (differentiableOn_cubicPrimeFactor p).comp
    (f := fun w : Fin 3 → ℂ => (w 0,w 1,w 2))
    (s := cubicCoordinateTube) he.differentiableOn (fun _ hw => hw)

private theorem differentiableOn_cubicCoordinatePrimeProduct (P : Finset Nat.Primes) :
    DifferentiableOn ℂ (fun w : Fin 3 → ℂ => ∏ p ∈ P, cubicPrimeFactor p (w 0) (w 1) (w 2))
      cubicCoordinateTube := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableOn_const (1 : ℂ)
  | @insert p S hp hS =>
    have h := differentiableOn_cubicCoordinatePrimeFactor p
    convert h.mul hS using 1 <;> try rfl
    funext w
    exact Finset.prod_insert hp

/-- Joint holomorphy, not merely separate pointwise convergence, through the critical plane. -/
theorem analyticOnNhd_cubicEulerCorrection :
    AnalyticOnNhd ℂ (fun w : Fin 3 → ℂ => cubicEulerCorrection (w 0) (w 1) (w 2))
      cubicCoordinateTube := by
  obtain ⟨P, hP⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset Nat.Primes))
  have hc := hasProdLocallyUniformlyOn_cubicPrimeFactor.comp
    (fun w : Fin 3 → ℂ => (w 0,w 1,w 2)) (fun _ hw => hw)
    ((continuous_apply 0).prodMk ((continuous_apply 1).prodMk (continuous_apply 2))).continuousOn
  have hconv : TendstoLocallyUniformlyOn
      (fun n => fun w : Fin 3 → ℂ => ∏ p ∈ P n, cubicPrimeFactor p (w 0) (w 1) (w 2))
      (fun w => cubicEulerCorrection (w 0) (w 1) (w 2)) Filter.atTop cubicCoordinateTube := by
    intro w hw r hr
    obtain ⟨t, ht, htr⟩ := hc w hw r hr
    exact ⟨t, ht, hP.eventually htr⟩
  apply GaloisForLFunctions.HTGeometry.analyticOnNhd_of_tendstoLocallyUniformlyOn
    isOpen_cubicCoordinateTube _ hconv
  exact fun n => differentiableOn_cubicCoordinatePrimeProduct (P n)

end RHTower.BAGTrace
