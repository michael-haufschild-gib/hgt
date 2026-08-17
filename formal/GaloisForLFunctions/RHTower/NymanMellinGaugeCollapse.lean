import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.HTGeometry.ComplexExponentialPolynomial
import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.ZetaHypertranscendence
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization

/-!
# The Mellin transform of the Nyman--Báez-Duarte generators
-/

namespace GaloisForLFunctions.NymanMellin

open MeasureTheory Set Complex GaloisForLFunctions RHTower

noncomputable section

/-- The Báez-Duarte / Nyman generator `ρ_a(x) = {1/(a x)}`. -/
def nymanGen (a : ℝ) : ℝ → ℂ := fun x => ((Int.fract (1 / (a * x)) : ℝ) : ℂ)

/-- The dilated fractional-part kernel `y ↦ {y/a}`. -/
def fractDilate (c : ℝ) : ℝ → ℂ := fun y => ((Int.fract (c * y) : ℝ) : ℂ)

theorem nymanGen_eq_comp_inv (a : ℝ) (x : ℝ) :
    nymanGen a x = fractDilate (1 / a) x⁻¹ := by
  have h : 1 / (a * x) = (1 / a) * x⁻¹ := by
    rw [one_div, one_div, mul_inv]
  simp only [nymanGen, fractDilate, h]

theorem mellinConvergent_fractDilate {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {c : ℝ} (hc : 0 < c) : MellinConvergent (fractDilate c) (-w) := by
  have hbase := integrableOn_Ioi_zero_fract_dilate_cpow hw0 hw1 hc
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp only [fractDilate, smul_eq_mul]
  rw [show (-w - 1 : ℂ) = -(w + 1) by ring]
  ring

theorem mellin_fractDilate {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) {c : ℝ} (hc : 0 < c) :
    mellin (fractDilate c) (-w) = ((c : ℝ) : ℂ) ^ w * (-(riemannZeta w / w)) := by
  rw [← integral_Ioi_zero_fract_dilate_cpow hw0 hw1 hc, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [fractDilate, smul_eq_mul]
  rw [show (-w - 1 : ℂ) = -(w + 1) by ring]
  ring

end

end GaloisForLFunctions.NymanMellin

namespace GaloisForLFunctions.NymanMellin

open MeasureTheory Set Complex GaloisForLFunctions RHTower

noncomputable section

theorem nymanGen_eq_fun {a : ℝ} : nymanGen a = fun t : ℝ => fractDilate (1 / a) t⁻¹ := by
  funext x
  exact nymanGen_eq_comp_inv a x

theorem mellin_nymanGen_aux {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ} (ha : 0 < a) :
    mellin (nymanGen a) s = ((1 / a : ℝ) : ℂ) ^ s * (-(riemannZeta s / s)) := by
  rw [nymanGen_eq_fun, mellin_comp_inv, mellin_fractDilate hs0 hs1 (by positivity)]

theorem ofReal_inv_cpow {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((1 / a : ℝ) : ℂ) ^ s = ((a : ℝ) : ℂ) ^ (-s) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have harg : ((a : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha.le]
    exact Real.pi_ne_zero.symm
  rw [one_div, Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]

/-- **The Mellin identity `(4)`.**  `M[ρ_a](s) = -a^{-s} ζ(s)/s` on the critical strip. -/
theorem mellin_nymanGen {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ} (ha : 0 < a) :
    mellin (nymanGen a) s = -(((a : ℝ) : ℂ) ^ (-s) * riemannZeta s / s) := by
  rw [mellin_nymanGen_aux hs0 hs1 ha, ofReal_inv_cpow ha]
  ring

theorem mellinConvergent_nymanGen {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ}
    (ha : 0 < a) : MellinConvergent (nymanGen a) s := by
  have hbase : MellinConvergent (fractDilate (1 / a)) (-s) :=
    mellinConvergent_fractDilate hs0 hs1 (by positivity)
  have hrpow : MellinConvergent (fun t : ℝ => fractDilate (1 / a) (t ^ (-1 : ℝ))) s := by
    rw [MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0)]
    have hdiv : s / (-1 : ℝ) = -s := by
      push_cast
      ring
    rwa [hdiv]
  refine hrpow.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have htpos : (0 : ℝ) < t := mem_Ioi.mp ht
  rw [nymanGen_eq_fun]
  simp only
  rw [Real.rpow_neg_one]

end

end GaloisForLFunctions.NymanMellin

namespace GaloisForLFunctions.NymanMellin

open MeasureTheory Set Complex GaloisForLFunctions RHTower

noncomputable section

/-- A finite Nyman--Báez-Duarte combination `g = ∑ c_j ρ_{a_j}`. -/
def nymanCombination {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) : ℝ → ℂ :=
  fun x => ∑ j, c j * nymanGen (a j) x

/-- The exponential-polynomial gauge `P_g(s) = ∑ c_j a_j^{-s}`. -/
def freqPoly {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (s : ℂ) : ℂ :=
  ∑ j, c j * ((a j : ℝ) : ℂ) ^ (-s)

theorem mellin_const_mul (c : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun x => c * f x) s = c * mellin f s := by
  rw [mellin, mellin, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul]
  ring

theorem mellinConvergent_const_mul {c : ℂ} {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    MellinConvergent (fun x => c * f x) s := by
  have := hf.const_smul (c := c)
  simpa [MellinConvergent, smul_eq_mul] using this

theorem mellinConvergent_nymanCombination {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ j, 0 < a j) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (nymanCombination c a) s := by
  have hterm : ∀ j : Fin m,
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (c j * nymanGen (a j) t)) (Ioi 0) := by
    intro j
    exact mellinConvergent_const_mul (mellinConvergent_nymanGen hs0 hs1 (ha j))
  have hsum : IntegrableOn
      (fun t : ℝ => ∑ j, (t : ℂ) ^ (s - 1) • (c j * nymanGen (a j) t)) (Ioi 0) :=
    integrable_finsetSum _ (fun j _ => hterm j)
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro t _
  simp only [nymanCombination, Finset.smul_sum]

/-- **The Mellin transform of a finite Nyman combination `(6)`.** -/
theorem mellin_nymanCombination {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ j, 0 < a j) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (nymanCombination c a) s = -(freqPoly c a s * riemannZeta s / s) := by
  have hterm : ∀ j : Fin m,
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (c j * nymanGen (a j) t)) (Ioi 0) := by
    intro j
    exact mellinConvergent_const_mul (mellinConvergent_nymanGen hs0 hs1 (ha j))
  have hsplit : mellin (nymanCombination c a) s = ∑ j, mellin (fun x => c j * nymanGen (a j) x) s := by
    rw [mellin]
    have hcongr : ∀ t ∈ Ioi (0 : ℝ),
        (t : ℂ) ^ (s - 1) • nymanCombination c a t
          = ∑ j, (t : ℂ) ^ (s - 1) • (c j * nymanGen (a j) t) := by
      intro t _
      simp only [nymanCombination, Finset.smul_sum]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_finsetSum _ (fun j _ => hterm j)]
    rfl
  rw [hsplit]
  have hval : ∀ j : Fin m, mellin (fun x => c j * nymanGen (a j) x) s
      = -(c j * ((a j : ℝ) : ℂ) ^ (-s) * riemannZeta s / s) := by
    intro j
    rw [mellin_const_mul, mellin_nymanGen hs0 hs1 (ha j)]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hval j), freqPoly]
  rw [show (fun j : Fin m => -(c j * ((a j : ℝ) : ℂ) ^ (-s) * riemannZeta s / s))
      = (fun j : Fin m => (c j * ((a j : ℝ) : ℂ) ^ (-s)) * (-(riemannZeta s / s))) from by
    funext j; ring]
  rw [← Finset.sum_mul]
  ring

end

end GaloisForLFunctions.NymanMellin

namespace GaloisForLFunctions.NymanMellin

open MeasureTheory Set Complex GaloisForLFunctions RHTower

noncomputable section

theorem ofReal_cpow_neg_eq_exp {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((a : ℝ) : ℂ) ^ (-s) = Complex.exp ((-((Real.log a : ℝ) : ℂ)) * s) := by
  have hne : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log ha.le]
  congr 1
  ring

theorem freqPoly_eq_expSum {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) :
    freqPoly c a
      = fun x : ℂ => ∑ j ∈ (Finset.univ : Finset (Fin m)),
          c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * x) := by
  funext s
  rw [freqPoly]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ofReal_cpow_neg_eq_exp (ha j)]

/-- **The exponential-polynomial gauge is differentially algebraic.** -/
theorem differentiallyAlgebraic_freqPoly {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ j, 0 < a j) : DifferentiallyAlgebraic (freqPoly c a) := by
  rw [freqPoly_eq_expSum c a ha]
  exact differentiallyAlgebraic_finset_expSum_general (Finset.univ : Finset (Fin m)) c
    (fun j => -((Real.log (a j) : ℝ) : ℂ))

theorem freqPoly_eq_cexpFn {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (s : ℂ) :
    freqPoly c a s
      = GaloisForLFunctions.HTGeometry.CExpPoly.cexpFn
          (fun j => -((Real.log (a j) : ℝ) : ℂ)) (fun j => Polynomial.C (c j)) s := by
  rw [freqPoly, GaloisForLFunctions.HTGeometry.CExpPoly.cexpFn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_C, ofReal_cpow_neg_eq_exp (ha j)]

/-- **The gauge is not identically zero.**  Exponentials with distinct real frequencies are
linearly independent. -/
theorem exists_freqPoly_ne_zero {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ j, 0 < a j) (hinj : Function.Injective a) (hc : ∃ j, c j ≠ 0) :
    ∃ s : ℂ, freqPoly c a s ≠ 0 := by
  obtain ⟨j₀, hj₀⟩ := hc
  have hm : m ≠ 0 := by
    intro h
    subst h
    exact (Fin.elim0 j₀)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  by_contra hcon
  push Not at hcon
  have hfreqinj : Function.Injective (fun j : Fin (m' + 1) => -((Real.log (a j) : ℝ) : ℂ)) := by
    intro i j hij
    simp only [neg_inj, Complex.ofReal_inj] at hij
    exact hinj (Real.log_injOn_pos (Set.mem_Ioi.mpr (ha i)) (Set.mem_Ioi.mpr (ha j)) hij)
  have hzero : ∀ z : ℂ, GaloisForLFunctions.HTGeometry.CExpPoly.cexpFn
      (fun j : Fin (m' + 1) => -((Real.log (a j) : ℝ) : ℂ))
      (fun j => Polynomial.C (c j)) z = 0 := by
    intro z
    rw [← freqPoly_eq_cexpFn c a ha z]
    exact hcon z
  have hP := GaloisForLFunctions.HTGeometry.CExpPoly.eq_zero_of_cexpFn_eq_zero m'
    (fun j : Fin (m' + 1) => -((Real.log (a j) : ℝ) : ℂ))
    (fun j => Polynomial.C (c j)) hfreqinj hzero j₀
  exact hj₀ (by simpa using congrArg (fun p : Polynomial ℂ => p.coeff 0) hP)

end

end GaloisForLFunctions.NymanMellin


namespace GaloisForLFunctions.NymanUpper

open Filter Set Topology
open scoped Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance nyUpperDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance nyUpperDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance nyUpperComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance nyUpperRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance nyUpperRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance nyUpperCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance nyUpperRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- An upper-end analytic germ built from a function analytic on some upper half-plane. -/
def upperAnalyticOf (f : ℂ → ℂ) {H : ℝ} (hf : AnalyticOnNhd ℂ f (upperTail H)) :
    upperEndAnalyticSubring :=
  ⟨Filter.Germ.coeRingHom upperEndFilter f, ⟨f, H, hf, rfl⟩⟩

/-- Its image in the upper-end meromorphic field. -/
def upperMeroOf (f : ℂ → ℂ) {H : ℝ} (hf : AnalyticOnNhd ℂ f (upperTail H)) :
    upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField (upperAnalyticOf f hf)

theorem upperAnalyticDeriv_upperAnalyticOf (f : ℂ → ℂ) {H : ℝ}
    (hf : AnalyticOnNhd ℂ f (upperTail H)) :
    upperEndAnalyticDeriv (upperAnalyticOf f hf) = upperAnalyticOf (deriv f) hf.deriv := by
  apply Subtype.ext
  rfl

theorem upperMeroOf_deriv (f : ℂ → ℂ) {H : ℝ} (hf : AnalyticOnNhd ℂ f (upperTail H)) :
    (upperMeroOf f hf)′ = upperMeroOf (deriv f) hf.deriv := by
  rw [upperMeroOf, upperEndMeroFieldDifferential_algebraMap,
    upperAnalyticDeriv_upperAnalyticOf]
  rfl


theorem upperAnalyticOf_congr {f g : ℂ → ℂ} {H K : ℝ}
    (hf : AnalyticOnNhd ℂ f (upperTail H)) (hg : AnalyticOnNhd ℂ g (upperTail K))
    (h : f = g) : upperAnalyticOf f hf = upperAnalyticOf g hg := by
  subst h
  apply Subtype.ext
  rfl

theorem upperMeroOf_congr {f g : ℂ → ℂ} {H K : ℝ}
    (hf : AnalyticOnNhd ℂ f (upperTail H)) (hg : AnalyticOnNhd ℂ g (upperTail K))
    (h : f = g) : upperMeroOf f hf = upperMeroOf g hg := by
  rw [upperMeroOf, upperMeroOf, upperAnalyticOf_congr hf hg h]

theorem upperAnalyticOf_add {f g : ℂ → ℂ} {H : ℝ}
    (hf : AnalyticOnNhd ℂ f (upperTail H)) (hg : AnalyticOnNhd ℂ g (upperTail H)) :
    upperAnalyticOf (fun z => f z + g z) (hf.add hg)
      = upperAnalyticOf f hf + upperAnalyticOf g hg := by
  apply Subtype.ext
  rfl

theorem upperAnalyticOf_mul {f g : ℂ → ℂ} {H : ℝ}
    (hf : AnalyticOnNhd ℂ f (upperTail H)) (hg : AnalyticOnNhd ℂ g (upperTail H)) :
    upperAnalyticOf (fun z => f z * g z) (hf.mul hg)
      = upperAnalyticOf f hf * upperAnalyticOf g hg := by
  apply Subtype.ext
  rfl

theorem upperMeroOf_add {f g : ℂ → ℂ} {H : ℝ}
    (hf : AnalyticOnNhd ℂ f (upperTail H)) (hg : AnalyticOnNhd ℂ g (upperTail H)) :
    upperMeroOf (fun z => f z + g z) (hf.add hg) = upperMeroOf f hf + upperMeroOf g hg := by
  rw [upperMeroOf, upperMeroOf, upperMeroOf, upperAnalyticOf_add, map_add]

theorem upperMeroOf_mul {f g : ℂ → ℂ} {H : ℝ}
    (hf : AnalyticOnNhd ℂ f (upperTail H)) (hg : AnalyticOnNhd ℂ g (upperTail H)) :
    upperMeroOf (fun z => f z * g z) (hf.mul hg) = upperMeroOf f hf * upperMeroOf g hg := by
  rw [upperMeroOf, upperMeroOf, upperMeroOf, upperAnalyticOf_mul, map_mul]

theorem analyticOnNhd_expLinear (lam : ℂ) (H : ℝ) :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (lam * z)) (upperTail H) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_upperTail H)
  intro z _
  have hdiff : Differentiable ℂ fun z : ℂ => Complex.exp (lam * z) := by
    fun_prop
  exact (hdiff z).differentiableWithinAt

theorem deriv_expLinear (lam : ℂ) :
    deriv (fun z : ℂ => Complex.exp (lam * z)) = fun z : ℂ => lam * Complex.exp (lam * z) := by
  funext z
  have h : HasDerivAt (fun w : ℂ => Complex.exp (lam * w)) (Complex.exp (lam * z) * lam) z := by
    simpa using (((hasDerivAt_id z).const_mul lam)).cexp
  rw [h.deriv]
  ring

/-- The upper-end germ of `exp(λ z)`. -/
def expMero (lam : ℂ) : upperEndMeroField :=
  upperMeroOf (fun z : ℂ => Complex.exp (lam * z)) (analyticOnNhd_expLinear lam 0)

theorem upperMeroOf_const (c : ℂ) :
    upperMeroOf (fun _ : ℂ => c) (analyticOnNhd_const (E := ℂ) (s := upperTail 0))
      = algebraMap ℂ upperEndMeroField c := by
  show algebraMap upperEndAnalyticSubring upperEndMeroField _ = upperEndComplexToMero c
  rw [upperEndComplexToMero, RingHom.comp_apply, upperEndPolyToMero, RingHom.comp_apply]
  congr 1
  apply Subtype.ext
  refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  simp

theorem expMero_deriv (lam : ℂ) :
    (expMero lam)′ = algebraMap ℂ upperEndMeroField lam * expMero lam := by
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => lam) (upperTail 0) := analyticOnNhd_const
  have hprod : AnalyticOnNhd ℂ (fun z : ℂ => lam * Complex.exp (lam * z)) (upperTail 0) :=
    hconst.mul (analyticOnNhd_expLinear lam 0)
  have h1 : upperMeroOf (deriv fun z : ℂ => Complex.exp (lam * z))
        (analyticOnNhd_expLinear lam 0).deriv
      = upperMeroOf (fun z : ℂ => lam * Complex.exp (lam * z)) hprod :=
    upperMeroOf_congr _ hprod (deriv_expLinear lam)
  rw [expMero, upperMeroOf_deriv, h1,
    upperMeroOf_mul hconst (analyticOnNhd_expLinear lam 0), upperMeroOf_const]

theorem upperAnalyticOf_sum {ι : Type*} [Fintype ι] (g : ι → ℂ → ℂ) {H : ℝ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (upperTail H))
    (hsum : AnalyticOnNhd ℂ (fun z => ∑ i, g i z) (upperTail H)) :
    upperAnalyticOf (fun z => ∑ i, g i z) hsum = ∑ i, upperAnalyticOf (g i) (hg i) := by
  apply Subtype.ext
  have hfun : (fun z : ℂ => ∑ i, g i z) = ∑ i, g i := by
    funext z
    simp
  show (Filter.Germ.coeRingHom upperEndFilter) (fun z : ℂ => ∑ i, g i z)
      = ((∑ i, upperAnalyticOf (g i) (hg i) : upperEndAnalyticSubring) :
          Filter.Germ upperEndFilter ℂ)
  rw [hfun, map_sum]
  push_cast
  rfl

theorem upperMeroOf_sum {ι : Type*} [Fintype ι] (g : ι → ℂ → ℂ) {H : ℝ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (upperTail H))
    (hsum : AnalyticOnNhd ℂ (fun z => ∑ i, g i z) (upperTail H)) :
    upperMeroOf (fun z => ∑ i, g i z) hsum = ∑ i, upperMeroOf (g i) (hg i) := by
  rw [upperMeroOf, upperAnalyticOf_sum g hg hsum, map_sum]
  rfl

/-- **The exponential germ is differentially algebraic over the rational coordinate field.** -/
theorem differentialAlgebraicOver_expMero (lam : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (expMero lam) := by
  classical
  refine differentialAlgebraicOver_of_finiteJetRelation
    (Q := (MvPolynomial.X 1 : MvPolynomial (Fin 2) (RatFunc ℂ))
      - MvPolynomial.C (algebraMap ℂ (RatFunc ℂ) lam) * MvPolynomial.X 0) ?_ ?_
  · intro h0
    have hc := congrArg (fun r : MvPolynomial (Fin 2) (RatFunc ℂ) =>
      MvPolynomial.coeff (Finsupp.single 1 1) r) h0
    simp [MvPolynomial.coeff_X', MvPolynomial.coeff_C_mul, Finsupp.single_eq_single_iff] at hc
  · have hjet0 : differentialJet 0 (expMero lam) = expMero lam := by simp
    have hjet1 : differentialJet 1 (expMero lam) = (expMero lam)′ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, differentialJet_succ]
      simp
    simp only [MvPolynomial.aeval_X, map_sub, map_mul, MvPolynomial.aeval_C,
      Fin.isValue, Fin.val_zero, Fin.val_one]
    rw [hjet0, hjet1, expMero_deriv]
    have halg : (algebraMap (RatFunc ℂ) upperEndMeroField) (algebraMap ℂ (RatFunc ℂ) lam)
        = algebraMap ℂ upperEndMeroField lam := by
      have hC : (algebraMap ℂ (RatFunc ℂ)) lam
          = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C lam) := by
        rw [RatFunc.algebraMap_C]
        rfl
      show upperEndRatfuncToMero (algebraMap ℂ (RatFunc ℂ) lam) = upperEndComplexToMero lam
      rw [hC, upperEndRatfuncToMero_algebraMap_polynomial]
      rfl
    rw [halg, sub_self]

/-- **Base change of differential algebraicity.**  A relation over a subfield is a relation over
any extension field. -/
theorem differentialAlgebraicOver_baseChange {F L K : Type*} [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K] [Differential K]
    {x : K} (hx : DifferentialAlgebraicOver F x) : DifferentialAlgebraicOver L x := by
  obtain ⟨n, Q, hQ0, hQann⟩ := exists_jet_relation_of_differentialAlgebraicOver hx
  refine differentialAlgebraicOver_of_finiteJetRelation
    (Q := Q.map (algebraMap F L)) ?_ ?_
  · intro h0
    refine hQ0 (MvPolynomial.map_injective _ (algebraMap F L).injective ?_)
    rw [h0, map_zero]
  · rw [MvPolynomial.aeval_map_algebraMap]
    exact hQann

theorem differentialAlgebraicOver_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → upperEndMeroField)
    (hf : ∀ i ∈ s, DifferentialAlgebraicOver (RatFunc ℂ) (f i)) :
    DifferentialAlgebraicOver (RatFunc ℂ) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using
        (differentialAlgebraicOver_algebraMap (F := RatFunc ℂ) (E := upperEndMeroField) 0)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact differentialAlgebraicOver_add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem differentialAlgebraicOver_complexConstant (c : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (algebraMap ℂ upperEndMeroField c) := by
  have halg : algebraMap ℂ upperEndMeroField c
      = algebraMap (RatFunc ℂ) upperEndMeroField (algebraMap ℂ (RatFunc ℂ) c) := by
    have hC : (algebraMap ℂ (RatFunc ℂ)) c
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) := by
      rw [RatFunc.algebraMap_C]
      rfl
    show upperEndComplexToMero c = upperEndRatfuncToMero (algebraMap ℂ (RatFunc ℂ) c)
    rw [hC, upperEndRatfuncToMero_algebraMap_polynomial]
    rfl
  rw [halg]
  exact differentialAlgebraicOver_algebraMap _

/-! ## The Nyman gauge in the upper-end meromorphic field -/

/-- The upper-end germ of the exponential-polynomial gauge `P_g`. -/
def freqPolyMero {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) : upperEndMeroField :=
  ∑ j, algebraMap ℂ upperEndMeroField (c j) * expMero (-((Real.log (a j) : ℝ) : ℂ))

theorem differentialAlgebraicOver_freqPolyMero {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (freqPolyMero c a) :=
  differentialAlgebraicOver_finsetSum _ _ fun j _ =>
    differentialAlgebraicOver_mul (differentialAlgebraicOver_complexConstant (c j))
      (differentialAlgebraicOver_expMero _)

theorem analyticOnNhd_freqPolySummand {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (j : Fin m) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z)) (upperTail 0) :=
  (analyticOnNhd_const).mul (analyticOnNhd_expLinear _ 0)

theorem analyticOnNhd_freqPolySum {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z))
      (upperTail 0) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_upperTail 0)
  intro z _
  have hd : Differentiable ℂ
      (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z)) := by
    fun_prop
  exact (hd z).differentiableWithinAt

theorem upperMeroOf_freqPolySum {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) :
    upperMeroOf (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z))
        (analyticOnNhd_freqPolySum c a)
      = freqPolyMero c a := by
  rw [upperMeroOf_sum _ (analyticOnNhd_freqPolySummand c a) (analyticOnNhd_freqPolySum c a),
    freqPolyMero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : upperMeroOf (fun z : ℂ => c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z))
        (analyticOnNhd_freqPolySummand c a j)
      = upperMeroOf (fun z : ℂ => (fun _ : ℂ => c j) z *
          (fun w : ℂ => Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * w)) z)
        ((analyticOnNhd_const).mul (analyticOnNhd_expLinear (-((Real.log (a j) : ℝ) : ℂ)) 0)) :=
    upperMeroOf_congr _ _ rfl
  rw [h1, upperMeroOf_mul analyticOnNhd_const (analyticOnNhd_expLinear _ 0), upperMeroOf_const]
  rfl

end

end GaloisForLFunctions.NymanUpper

namespace GaloisForLFunctions.NymanUpper

open Filter Set Topology
open scoped Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance nyUpperDomain' : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance nyUpperDifferential' : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance nyUpperComplexAlgebra' : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance nyUpperRatAlgebra' : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance nyUpperRatFuncDifferential' : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance nyUpperCharZero' : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance nyUpperRatFuncDifferentialAlgebra' :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- **The gauge germ is nonzero.** -/
theorem freqPolyMero_ne_zero {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (hpos : ∀ j, 0 < a j) (hinj : Function.Injective a) (hc : ∃ j, c j ≠ 0) :
    freqPolyMero c a ≠ 0 := by
  intro h0
  have hmero : upperMeroOf
      (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z))
      (analyticOnNhd_freqPolySum c a) = 0 := by
    rw [upperMeroOf_freqPolySum, h0]
  have hanal : upperAnalyticOf
      (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z))
      (analyticOnNhd_freqPolySum c a) = 0 :=
    IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
      (by rw [← upperMeroOf]; rw [hmero, map_zero])
  have hgerm : ((fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z)) :
      Filter.Germ upperEndFilter ℂ) = 0 := by
    have h2 := congrArg Subtype.val hanal
    rwa [ZeroMemClass.coe_zero] at h2
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at hgerm
  have hgerm' : ∀ᶠ z in upperEndFilter,
      (∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z)) = 0 := hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm'
  obtain ⟨H, -, hH⟩ := hgerm'
  obtain ⟨s, hs⟩ := NymanMellin.exists_freqPoly_ne_zero c a hpos hinj hc
  apply hs
  have hentire : AnalyticOnNhd ℂ
      (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z))
      (Set.univ) := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    intro z _
    have hd : Differentiable ℂ
        (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z)) := by
      fun_prop
    exact (hd z).differentiableWithinAt
  have hz₀ : (Complex.I * ((H + 1 : ℝ) : ℂ)) ∈ upperTail H := by
    show H < (Complex.I * ((H + 1 : ℝ) : ℂ)).im
    simp
  have hev : (fun z : ℂ => ∑ j, c j * Complex.exp ((-((Real.log (a j) : ℝ) : ℂ)) * z))
      =ᶠ[nhds (Complex.I * ((H + 1 : ℝ) : ℂ))] 0 := by
    filter_upwards [(isOpen_upperTail H).mem_nhds hz₀] with z hz
    exact hH hz
  have hzero := hentire.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ (Complex.I * ((H + 1 : ℝ) : ℂ))) hev
  rw [NymanMellin.freqPoly_eq_expSum c a hpos]
  exact hzero (Set.mem_univ s)

end

end GaloisForLFunctions.NymanUpper

namespace GaloisForLFunctions.NymanUpper

open Filter Set Topology
open scoped Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance nyFinDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance nyFinDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance nyFinComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance nyFinRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance nyFinRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance nyFinCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance nyFinRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

local instance nyFinGammaFieldDifferentialAlgebra :
    DifferentialAlgebra ↥(gammaCoefficientField) upperEndMeroField where
  deriv_algebraMap _ := rfl

/-- Base change of a rational differential relation to the Gamma coefficient field. -/
theorem differentialAlgebraicOver_gammaField_of_ratFunc {x : upperEndMeroField}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver ↥(gammaCoefficientField) x := by
  obtain ⟨n, Q, hQ0, hQann⟩ := exists_jet_relation_of_differentialAlgebraicOver hx
  refine differentialAlgebraicOver_of_finiteJetRelation
    (Q := Q.map (algebraMap (RatFunc ℂ) ↥(gammaCoefficientField))) ?_ ?_
  · intro h0
    refine hQ0 (MvPolynomial.map_injective _
      (algebraMap (RatFunc ℂ) ↥(gammaCoefficientField)).injective ?_)
    rw [h0, map_zero]
  · rw [MvPolynomial.aeval_map_algebraMap]
    exact hQann

/-- The upper-end germ of `ζ`. -/
def zetaUpperMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic

/-- The upper-end germ of the meromorphic continuation of the Mellin transform of a finite
Nyman combination: `M[g] = -P_g·ζ/s`. -/
def nymanMellinMero {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) : upperEndMeroField :=
  -(freqPolyMero c a * zetaUpperMero * (upperEndCoordinateMero)⁻¹)

theorem upperEndCoordinateMero_ne_zero : upperEndCoordinateMero ≠ 0 := by
  intro hcon
  exact Polynomial.X_ne_zero
    (upperEndPolyToMero_injective (hcon.trans (map_zero upperEndPolyToMero).symm))

/-- **Every nonzero finite Nyman approximant has a hypertranscendental Mellin transform.**
The whole zeta factor survives every finite approximation, so no finite Nyman combination has a
differentially algebraic Mellin transform. -/
theorem hypertranscendentalOver_nymanMellinMero {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (hpos : ∀ j, 0 < a j) (hinj : Function.Injective a) (hc : ∃ j, c j ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ) (nymanMellinMero c a) := by
  intro hDA
  have hP : freqPolyMero c a ≠ 0 := freqPolyMero_ne_zero c a hpos hinj hc
  have hs : upperEndCoordinateMero ≠ 0 := upperEndCoordinateMero_ne_zero
  have hzeta : zetaUpperMero
      = -(nymanMellinMero c a) * upperEndCoordinateMero * (freqPolyMero c a)⁻¹ := by
    rw [nymanMellinMero, neg_neg]
    calc zetaUpperMero
        = zetaUpperMero * (upperEndCoordinateMero⁻¹ * upperEndCoordinateMero)
            * (freqPolyMero c a * (freqPolyMero c a)⁻¹) := by
          rw [inv_mul_cancel₀ hs, mul_inv_cancel₀ hP, mul_one, mul_one]
      _ = freqPolyMero c a * zetaUpperMero * upperEndCoordinateMero⁻¹
            * upperEndCoordinateMero * (freqPolyMero c a)⁻¹ := by
          ring
  have hcoord : upperEndCoordinateMero
      = algebraMap (RatFunc ℂ) upperEndMeroField (RatFunc.X) := by
    show upperEndPolyToMero Polynomial.X = upperEndRatfuncToMero RatFunc.X
    rw [← RatFunc.algebraMap_X, upperEndRatfuncToMero_algebraMap_polynomial]
  have hDAcoord : DifferentialAlgebraicOver (RatFunc ℂ) upperEndCoordinateMero := by
    rw [hcoord]
    exact differentialAlgebraicOver_algebraMap _
  have hDAneg : DifferentialAlgebraicOver (RatFunc ℂ) (-(nymanMellinMero c a)) := by
    have hneg : -(nymanMellinMero c a)
        = algebraMap (RatFunc ℂ) upperEndMeroField (-1) * nymanMellinMero c a := by
      rw [map_neg, map_one]
      ring
    rw [hneg]
    exact differentialAlgebraicOver_mul (differentialAlgebraicOver_algebraMap _) hDA
  have hDAzeta : DifferentialAlgebraicOver (RatFunc ℂ) zetaUpperMero := by
    rw [hzeta]
    exact differentialAlgebraicOver_mul
      (differentialAlgebraicOver_mul hDAneg hDAcoord)
      (differentialAlgebraicOver_inv (differentialAlgebraicOver_freqPolyMero c a))
  exact zeta_hypertranscendentalOver_gammaCoefficientField (σ := 2) (by norm_num)
    (differentialAlgebraicOver_gammaField_of_ratFunc hDAzeta)

end

end GaloisForLFunctions.NymanUpper

namespace GaloisForLFunctions.NymanUpper

open Filter Set Topology
open scoped Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance nyGDomain : IsDomain upperEndAnalyticSubring := isDomain_upperEndAnalyticSubring
local instance nyGDifferential : Differential upperEndMeroField := upperEndMeroFieldDifferential
local instance nyGComplexAlgebra : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
local instance nyGRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

theorem zetaUpperMero_ne_zero : zetaUpperMero ≠ 0 := by
  intro h0
  have hanal : zetaUpperAnalytic = 0 :=
    IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
      (by rw [← zetaUpperMero]; rw [h0, map_zero])
  have hgerm : ((riemannZeta : ℂ → ℂ) : Filter.Germ upperEndFilter ℂ) = 0 := by
    have h2 := congrArg Subtype.val hanal
    rwa [ZeroMemClass.coe_zero] at h2
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at hgerm
  have hgerm' : ∀ᶠ z in upperEndFilter, riemannZeta z = 0 := hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm'
  obtain ⟨H, -, hH⟩ := hgerm'
  have hmem : ((2 : ℂ) + Complex.I * ((H + 1 : ℝ) : ℂ)) ∈ upperTail H := by
    show H < ((2 : ℂ) + Complex.I * ((H + 1 : ℝ) : ℂ)).im
    simp
  have hne : riemannZeta ((2 : ℂ) + Complex.I * ((H + 1 : ℝ) : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    show (1 : ℝ) < ((2 : ℂ) + Complex.I * ((H + 1 : ℝ) : ℂ)).re
    simp
  exact hne (hH hmem)

/-- **(10) One differentially algebraic gauge class.**  Any two nonzero finite Nyman Mellin
transforms differ exactly by the ratio of their exponential-polynomial gauges. -/
theorem nymanMellinMero_div {m n : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (d : Fin n → ℂ) (b : Fin n → ℝ) :
    nymanMellinMero c a / nymanMellinMero d b = freqPolyMero c a / freqPolyMero d b := by
  have hz : zetaUpperMero ≠ 0 := zetaUpperMero_ne_zero
  have hs : upperEndCoordinateMero ≠ 0 := upperEndCoordinateMero_ne_zero
  have hcommon : zetaUpperMero * upperEndCoordinateMero⁻¹ ≠ 0 :=
    mul_ne_zero hz (inv_ne_zero hs)
  rw [nymanMellinMero, nymanMellinMero, neg_div_neg_eq,
    mul_assoc (freqPolyMero c a), mul_assoc (freqPolyMero d b),
    mul_div_mul_right _ _ hcommon]

end

end GaloisForLFunctions.NymanUpper

namespace GaloisForLFunctions.NymanMellin

open MeasureTheory Set Complex GaloisForLFunctions RHTower

noncomputable section

/-- The Nyman--Beurling target `χ = 1_(0,1]`. -/
def nymanTarget : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => 1)

/-- **(11) The target has the rational Mellin transform `1/s`.** -/
theorem mellin_nymanTarget {s : ℂ} (hs : 0 < s.re) : mellin nymanTarget s = 1 / s := by
  have hne : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl 0 hs
  have hcongr : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • nymanTarget t
      = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t : ℝ => (t : ℂ) ^ (s - 1)) t := by
    intro t _
    rw [nymanTarget]
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_one]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hcongr,
    setIntegral_indicator measurableSet_Ioc]
  have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := by
    rw [Set.inter_eq_right]
    exact fun x hx => hx.1
  rw [hinter, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by rw [Complex.sub_re, Complex.one_re]; linarith))]
  rw [show (s - 1 + 1 : ℂ) = s by ring, Complex.ofReal_one, Complex.one_cpow,
    Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero]

end

end GaloisForLFunctions.NymanMellin
