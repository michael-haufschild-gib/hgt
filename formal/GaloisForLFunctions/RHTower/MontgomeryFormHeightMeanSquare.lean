import GaloisForLFunctions.RHTower.LorentzianComplexShiftProduct
import GaloisForLFunctions.RHTower.MontgomeryFormLogScaleMeanSquare
import GaloisForLFunctions.RHTower.MontgomeryLemmaOne

/-!
# Montgomery's pair form as a height mean square

For a finite family of points `ρ_j = β_j + iγ_j` in the strip `0 < β < 1` and a scale `x > 0`,
Montgomery's pair form `F(x) = Σ_{j,k} x^{ρ_j + ρ̄_k − 1} w(ρ_j + ρ̄_k − 1)`, `w(u) = 4/(4 − u²)`,
equals `(2/π) ∫_ℝ |Σ_j x^{ρ_j − 1/2} / (1 + ((t − γ_j) + i(β_j − 1/2))²)|² dt`.

The mechanism is the complex-shift Lorentzian product integral
`∫ 1/(1+(t+a)²) · 1/(1+(t+b)²) dt = 2π/(4 + (a − b)²)` applied to the shifts `a = i(ρ_j − 1/2)`
and `b = conj (i(ρ_k − 1/2))`, for which `4 + (a − b)² = 4 − (ρ_j + ρ̄_k − 1)²` is exactly the
denominator of Montgomery's weight.  The identity holds without any hypothesis on the real parts
beyond `0 < β < 1`, and is the bridge between the pair form and the `t`-integral of the zero side
of Montgomery's lemma: the summand `2x^ρ/((ρ − a_t)(ρ − b_t))` of that lemma is
`−2 √x · x^{ρ − 1/2} / (1 + (t + i(ρ − 1/2))²)`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower

/-! ## Lorentzian centres of zeros -/

/-- The Lorentzian centre `i(ρ − 1/2)` of a point `ρ`: `t + i(ρ − 1/2) = (t − Im ρ) + i(Re ρ − 1/2)`. -/
noncomputable def lorentzCentre (ρ : ℂ) : ℂ := I * (ρ - 1 / 2)

theorem lorentzCentre_re (ρ : ℂ) : (lorentzCentre ρ).re = -ρ.im := by
  simp [lorentzCentre]

theorem lorentzCentre_im (ρ : ℂ) : (lorentzCentre ρ).im = ρ.re - 1 / 2 := by
  simp [lorentzCentre]

theorem lorentzCentre_mem_unitStrip {ρ : ℂ} (hρ : 0 < ρ.re ∧ ρ.re < 1) :
    lorentzCentre ρ ∈ unitStrip := by
  rw [mem_unitStrip, lorentzCentre_im, abs_lt]
  constructor <;> linarith [hρ.1, hρ.2]

theorem conj_mem_unitStrip {b : ℂ} (hb : b ∈ unitStrip) : (starRingEnd ℂ) b ∈ unitStrip := by
  rw [mem_unitStrip] at hb ⊢
  simpa using hb

theorem conj_lorentzShift (a : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (lorentzShift a t) = lorentzShift ((starRingEnd ℂ) a) t := by
  simp [lorentzShift]

/-- `(i(ρ − 1/2) − conj(i(ρ' − 1/2)))² = −(ρ + ρ̄' − 1)²`. -/
theorem lorentzCentre_sub_conj_sq (ρ ρ' : ℂ) :
    (lorentzCentre ρ - (starRingEnd ℂ) (lorentzCentre ρ')) ^ 2
      = -(ρ + (starRingEnd ℂ) ρ' - 1) ^ 2 := by
  have h : lorentzCentre ρ - (starRingEnd ℂ) (lorentzCentre ρ')
      = I * (ρ + (starRingEnd ℂ) ρ' - 1) := by
    simp only [lorentzCentre, map_mul, Complex.conj_I, map_sub, map_div₀, map_one, map_ofNat]
    ring
  rw [h, mul_pow, I_sq]; ring

/-- The Montgomery zero summand is `−2 x^ρ` times the Lorentzian at the centre `i(ρ − 1/2)`. -/
theorem montgomeryZeroTerm_eq_lorentz (x t : ℝ) (q : XiZeroCopy) :
    montgomeryZeroTerm x t q
      = -2 * (x : ℂ) ^ (q.1 : ℂ) * lorentzShift (lorentzCentre (q.1 : ℂ)) t := by
  have hD : ((q.1 : ℂ) - montgomeryPoleUp t) * ((q.1 : ℂ) - montgomeryPoleDown t)
      = -(1 + ((t : ℂ) + lorentzCentre (q.1 : ℂ)) ^ 2) := by
    simp only [montgomeryPoleUp, montgomeryPoleDown, lorentzCentre]
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  rw [montgomeryZeroTerm, hD, div_neg, lorentzShift]
  ring

/-- `x^ρ = x^{1/2} · x^{ρ − 1/2}` for `x > 0`. -/
theorem cpow_eq_sqrt_mul (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ) ^ ρ = (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (ρ - 1 / 2) := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]
  congr 1
  push_cast; ring

/-! ## The Lorentzian zero sum -/

/-- The Lorentzian zero sum `Σ_j x^{ρ_j − 1/2} / (1 + (t + i(ρ_j − 1/2))²)` at height `t`. -/
noncomputable def lorentzZeroSum {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (x t : ℝ) : ℂ :=
  ∑ j ∈ s, (x : ℂ) ^ (ρ j - 1 / 2) * lorentzShift (lorentzCentre (ρ j)) t

/-- The pair integrand `x^{ρ_j + ρ̄_k − 1} · L_{a_j}(t) · L_{conj a_k}(t)`. -/
noncomputable def lorentzPairIntegrand {ι : Type*} (ρ : ι → ℂ) (x : ℝ) (j k : ι) (t : ℝ) : ℂ :=
  (x : ℂ) ^ (ρ j + (starRingEnd ℂ) (ρ k) - 1) *
    (lorentzShift (lorentzCentre (ρ j)) t * lorentzShift ((starRingEnd ℂ) (lorentzCentre (ρ k))) t)

theorem conj_ofReal_cpow_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ w) = (x : ℂ) ^ ((starRingEnd ℂ) w) := by
  rw [Complex.cpow_conj, Complex.conj_ofReal]
  rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm

theorem ofReal_cpow_mul_conj_cpow {x : ℝ} (hx : 0 < x) (u v : ℂ) :
    (x : ℂ) ^ u * (starRingEnd ℂ) ((x : ℂ) ^ v) = (x : ℂ) ^ (u + (starRingEnd ℂ) v) := by
  rw [conj_ofReal_cpow_pos hx, Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]

/-- `|Σ_j c_j(t)|²` expanded as the double sum of pair integrands. -/
theorem normSq_lorentzZeroSum_eq {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {x : ℝ} (hx : 0 < x)
    (t : ℝ) :
    ((‖lorentzZeroSum s ρ x t‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ s, ∑ k ∈ s, lorentzPairIntegrand ρ x j k t := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, lorentzZeroSum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [lorentzPairIntegrand, map_mul, conj_lorentzShift]
  have := ofReal_cpow_mul_conj_cpow hx (ρ j - 1 / 2) (ρ k - 1 / 2)
  have hexp : ρ j - 1 / 2 + (starRingEnd ℂ) (ρ k - 1 / 2) = ρ j + (starRingEnd ℂ) (ρ k) - 1 := by
    rw [map_sub, map_div₀, map_one, map_ofNat]; ring
  rw [hexp] at this
  rw [← this]; ring

/-- A uniform bound for the Lorentzian at a strip shift. -/
theorem norm_lorentzShift_le_const {a : ℂ} (ha : a ∈ unitStrip) (t : ℝ) :
    ‖lorentzShift a t‖ ≤ 4 / (1 - |a.im|) ^ 2 := by
  refine (norm_lorentzShift_le ha t).trans ?_
  have hη : 0 < 1 - |a.im| := by rw [mem_unitStrip] at ha; linarith
  have : 1 / (1 + (t + a.re) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (t + a.re)]
  calc (4 / (1 - |a.im|) ^ 2) * (1 / (1 + (t + a.re) ^ 2)) ≤ (4 / (1 - |a.im|) ^ 2) * 1 := by
        gcongr
    _ = _ := mul_one _

theorem integrable_lorentzShift_mul {a b : ℂ} (ha : a ∈ unitStrip) (hb : b ∈ unitStrip) :
    Integrable (fun t : ℝ => lorentzShift a t * lorentzShift b t) :=
  (integrable_lorentzShift hb).bdd_mul (continuous_lorentzShift ha).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_lorentzShift_le_const ha t)

theorem integrable_lorentzPairIntegrand {ι : Type*} (ρ : ι → ℂ) (x : ℝ) {j k : ι}
    (hj : 0 < (ρ j).re ∧ (ρ j).re < 1) (hk : 0 < (ρ k).re ∧ (ρ k).re < 1) :
    Integrable (lorentzPairIntegrand ρ x j k) :=
  (integrable_lorentzShift_mul (lorentzCentre_mem_unitStrip hj)
    (conj_mem_unitStrip (lorentzCentre_mem_unitStrip hk))).const_mul _

/-- The pair integrand integrates to `(π/2) · x^{u} w(u)`, `u = ρ_j + ρ̄_k − 1`. -/
theorem integral_lorentzPairIntegrand {ι : Type*} (ρ : ι → ℂ) (x : ℝ) {j k : ι}
    (hj : 0 < (ρ j).re ∧ (ρ j).re < 1) (hk : 0 < (ρ k).re ∧ (ρ k).re < 1) :
    ∫ t : ℝ, lorentzPairIntegrand ρ x j k t
      = ((Real.pi / 2 : ℝ) : ℂ) *
        ((x : ℂ) ^ (ρ j + (starRingEnd ℂ) (ρ k) - 1) *
          montgomeryWeight (ρ j + (starRingEnd ℂ) (ρ k) - 1)) := by
  have ha := lorentzCentre_mem_unitStrip hj
  have hb := conj_mem_unitStrip (lorentzCentre_mem_unitStrip hk)
  have hne := four_add_sq_ne_zero ha hb
  rw [lorentzCentre_sub_conj_sq] at hne
  unfold lorentzPairIntegrand
  rw [integral_const_mul, lorentzProduct_eq ha hb, lorentzCentre_sub_conj_sq, montgomeryWeight]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hne' : (4 : ℂ) - (ρ j + (starRingEnd ℂ) (ρ k) - 1) ^ 2 ≠ 0 := by
    intro h; apply hne; rw [← h]; ring
  push_cast
  field_simp
  ring

/-- **Montgomery's pair form as a height mean square.**  For a finite family in the strip
`0 < Re ρ < 1` and `x > 0`,
`F(x) = (2/π) ∫_ℝ |Σ_j x^{ρ_j − 1/2} / (1 + (t + i(ρ_j − 1/2))²)|² dt`. -/
theorem montgomeryForm_eq_integral_height {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {x : ℝ}
    (hx : 0 < x) (hρ : ∀ j ∈ s, 0 < (ρ j).re ∧ (ρ j).re < 1) :
    montgomeryForm s ρ x
      = ((2 / Real.pi : ℝ) : ℂ) * ∫ t : ℝ, ((‖lorentzZeroSum s ρ x t‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [normSq_lorentzZeroSum_eq s ρ hx]
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _
    (fun k hk => integrable_lorentzPairIntegrand ρ x (hρ j hj) (hρ k hk)))]
  rw [montgomeryForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ (fun k hk => integrable_lorentzPairIntegrand ρ x (hρ j hj) (hρ k hk)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_lorentzPairIntegrand ρ x (hρ j hj) (hρ k hk)]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- The real form: `Re F(x) = (2/π) ∫ |Σ_j …|² dt`; the imaginary part vanishes. -/
theorem montgomeryForm_re_eq_integral_height {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {x : ℝ}
    (hx : 0 < x) (hρ : ∀ j ∈ s, 0 < (ρ j).re ∧ (ρ j).re < 1) :
    (montgomeryForm s ρ x).re = (2 / Real.pi) * ∫ t : ℝ, ‖lorentzZeroSum s ρ x t‖ ^ 2 := by
  rw [montgomeryForm_eq_integral_height s ρ hx hρ]
  have : (∫ t : ℝ, ((‖lorentzZeroSum s ρ x t‖ ^ 2 : ℝ) : ℂ))
      = ((∫ t : ℝ, ‖lorentzZeroSum s ρ x t‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (integral_ofReal (𝕜 := ℂ))
  rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]

end RHTower
