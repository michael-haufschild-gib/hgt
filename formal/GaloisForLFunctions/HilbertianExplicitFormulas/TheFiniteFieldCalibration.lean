import GaloisForLFunctions.HilbertianExplicitFormulas.TheExplicitImageIsTheWeilForm
import GaloisForLFunctions.HilbertianExplicitFormulas.HolomorphicClocksCarryNoQuantum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues

/-!
# The `𝔽_q` calibration of same-point carriers

On a curve datum (normalized Frobenius eigenvalues `β_i`, closed under conjugation and `β ↦ 1/β`)
line reflection is the circle reflection `β ↦ 1/conj β = β/|β|²`. It keeps the argument of `β`, so
the argument plays the role of the ordinate, and an eigenvalue off the unit circle shares its
argument with its reflection. Hence:

* **Quantum law over `𝔽_q`.** The collision charge (ordered pairs of distinct eigenvalues on a
  common ray) is even, vanishes exactly on unitary data, and is at least `2` otherwise; the golden
  datum `q = 5`, `β = φ, φ⁻¹` realizes exactly `2`.
* **Lefschetz pencil.** The point-count power sums `∑ β_i^n` form the holomorphic pencil; their Cesàro
  mean square is bounded exactly on unitary data, i.e. exactly below the quantum.
* **Calibration rigidity on the circle.** A weight holomorphic on `ℂ*` that equals `|f|²` on the unit
  circle is `f(w) · conj f(1/conj w)`; every unitary-calibrated explicit formula on curve data is the
  Rosati pairing `∑ f(β_i) conj f(β_{refl i})`.

Weil's theorem says every curve over `𝔽_q` is unitary; these statements are the calibration of the
`ℤ` theory against it.
-/

open Complex Filter Topology Finset

namespace GaloisForLFunctions.HilbertianExplicitFormulas

open ArithmeticCastelnuovoSeveri (CurveDatum goldenDatum circleReflect)

noncomputable section

/-! ## Calibration rigidity on the unit circle -/

/-- `exp (i conj z) = 1 / conj (exp (i z))`: line reflection in `z` is circle reflection in
`w = exp (i z)`. -/
theorem exp_I_mul_conj (z : ℂ) :
    Complex.exp (I * (starRingEnd ℂ) z) = circleReflect (Complex.exp (I * z)) := by
  rw [circleReflect, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp

/-- **Calibration rigidity on the circle.** Weights holomorphic on `ℂ*` with `h = |f|²` on the unit
circle satisfy `h w = f w · conj (f (circleReflect w))` for every `w ≠ 0`. -/
theorem eq_rosatiWeight_of_circleCalibrated {f h : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {0}ᶜ) (hh : DifferentiableOn ℂ h {0}ᶜ)
    (hcal : ∀ w : ℂ, ‖w‖ = 1 → h w = ((‖f w‖ ^ 2 : ℝ) : ℂ)) {w : ℂ} (hw : w ≠ 0) :
    h w = f w * (starRingEnd ℂ) (f (circleReflect w)) := by
  have hexp : Differentiable ℂ fun z : ℂ => Complex.exp (I * z) :=
    (differentiable_const I |>.mul differentiable_id).cexp
  have hmem : ∀ z : ℂ, Complex.exp (I * z) ∈ ({0}ᶜ : Set ℂ) := fun z => Complex.exp_ne_zero _
  have hΦ : Differentiable ℂ fun z => f (Complex.exp (I * z)) := fun z =>
    (hf.differentiableAt (isOpen_compl_singleton.mem_nhds (hmem z))).comp z (hexp z)
  have hH : Differentiable ℂ fun z => h (Complex.exp (I * z)) := fun z =>
    (hh.differentiableAt (isOpen_compl_singleton.mem_nhds (hmem z))).comp z (hexp z)
  have hline : ∀ x : ℝ, h (Complex.exp (I * x)) = ((‖f (Complex.exp (I * x))‖ ^ 2 : ℝ) : ℂ) :=
    fun x => hcal _ (by rw [mul_comm, Complex.norm_exp_ofReal_mul_I])
  have hrig := eq_weilWeight_of_calibrated hΦ hH hline
  -- Choose a logarithm: `w = exp (i z)` with `z = -i log w`.
  have hz : Complex.exp (I * (-I * Complex.log w)) = w := by
    rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, I_mul_I, neg_neg], one_mul,
      Complex.exp_log hw]
  have := congrFun hrig (-I * Complex.log w)
  rw [weilWeight, RHTower.xiWeilSharp, exp_I_mul_conj, hz] at this
  exact this

/-! ## Curve data -/

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The argument `β / |β|` of a normalized eigenvalue: the ordinate over `𝔽_q`. -/
def curveOrdinate (i : ι) : ℂ := D.β i / (‖D.β i‖ : ℂ)

theorem circleReflect_eq (β : ℂ) :
    circleReflect β = β / ((‖β‖ ^ 2 : ℝ) : ℂ) := by
  rw [circleReflect, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj,
    Complex.normSq_eq_norm_sq, div_eq_mul_inv, Complex.ofReal_inv]

/-- Circle reflection keeps the ordinate. -/
theorem curveOrdinate_reflPerm (i : ι) : curveOrdinate D (D.reflPerm i) = curveOrdinate D i := by
  have hβ := D.β_ne_zero i
  have hn : ‖D.β i‖ ≠ 0 := norm_ne_zero_iff.mpr hβ
  rw [curveOrdinate, curveOrdinate, D.β_reflPerm, circleReflect_eq _, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  push_cast
  field_simp

/-- An eigenvalue off the unit circle differs from its reflection. -/
theorem β_reflPerm_ne_of_norm_ne_one {i : ι} (h : ‖D.β i‖ ≠ 1) : D.β (D.reflPerm i) ≠ D.β i := by
  intro heq
  apply h
  have hpos : 0 < ‖D.β i‖ := norm_pos_iff.mpr (D.β_ne_zero i)
  rw [D.β_reflPerm, circleReflect_eq] at heq
  have hn := congrArg norm heq
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_eq_iff (by positivity)] at hn
  have hsq : ‖D.β i‖ ^ 2 = 1 := by
    have := mul_left_cancel₀ hpos.ne' (hn.symm.trans (mul_one _).symm)
    exact this
  nlinarith

/-- Collision charge of a curve datum: ordered pairs of distinct eigenvalues on a common ray. -/
def curveCollisionCharge : ℕ :=
  ((univ ×ˢ univ : Finset (ι × ι)).filter fun p =>
    curveOrdinate D p.1 = curveOrdinate D p.2 ∧ D.β p.1 ≠ D.β p.2).card

/-- Unitary data have no collisions: on the circle the ordinate is the eigenvalue. -/
theorem curveCollisionCharge_eq_zero_of_unitary (hD : ∀ i, ‖D.β i‖ = 1) :
    curveCollisionCharge D = 0 := by
  rw [curveCollisionCharge, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, j⟩ - ⟨hord, hne⟩
  apply hne
  simpa [curveOrdinate, hD i, hD j] using hord

/-- **Quantum over `𝔽_q`.** An eigenvalue off the circle and its reflection collide twice. -/
theorem two_le_curveCollisionCharge [DecidableEq ι] {i : ι} (h : ‖D.β i‖ ≠ 1) :
    2 ≤ curveCollisionCharge D := by
  have hne := β_reflPerm_ne_of_norm_ne_one D h
  have hij : D.reflPerm i ≠ i := fun he => hne (by rw [he])
  have hsub : ({(i, D.reflPerm i), (D.reflPerm i, i)} : Finset (ι × ι)) ⊆
      (univ ×ˢ univ).filter fun p =>
        curveOrdinate D p.1 = curveOrdinate D p.2 ∧ D.β p.1 ≠ D.β p.2 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_filter.mpr ⟨by simp, (curveOrdinate_reflPerm D i).symm, hne.symm⟩
    · rw [Finset.mem_singleton.mp hp]
      exact Finset.mem_filter.mpr ⟨by simp, curveOrdinate_reflPerm D i, hne⟩
  have hcard : ({(i, D.reflPerm i), (D.reflPerm i, i)} : Finset (ι × ι)).card = 2 := by
    rw [Finset.card_pair]
    intro he
    exact hij (congrArg Prod.fst he).symm
  rw [curveCollisionCharge, ← hcard]
  exact Finset.card_le_card hsub

/-- **The quantum law over `𝔽_q`.** Unitarity, zero charge and charge below `2` coincide. -/
theorem unitary_tfae [DecidableEq ι] :
    List.TFAE [∀ i, ‖D.β i‖ = 1, curveCollisionCharge D = 0, curveCollisionCharge D < 2] := by
  tfae_have 1 → 2 := curveCollisionCharge_eq_zero_of_unitary D
  tfae_have 2 → 3 := fun h => by omega
  tfae_have 3 → 1 := fun h => by
    by_contra hD
    simp only [not_forall] at hD
    obtain ⟨i, hi⟩ := hD
    exact absurd (two_le_curveCollisionCharge D hi) (by omega)
  tfae_finish

/-- The collision charge of a curve datum is even (the swap pairs its ordered pairs). -/
theorem even_curveCollisionCharge : Even (curveCollisionCharge D) := by
  rw [curveCollisionCharge, ← ZMod.natCast_eq_zero_iff_even, Finset.card_eq_sum_ones,
    Nat.cast_sum]
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p hp _ => ?_)
    (fun p hp => ?_) (fun p _ => Prod.swap_swap p)
  · rw [Nat.cast_one, ← two_mul, mul_one]; decide
  · obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hp
    intro hfix
    exact hne (by rw [← congrArg Prod.snd hfix]; rfl)
  · obtain ⟨-, hord, hne⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨by simp, hord.symm, hne.symm⟩

/-- **Lefschetz pencil.** The point-count power sums `∑ β_i^n` have bounded Cesàro mean square
exactly on unitary data. -/
theorem cesaroBounded_lefschetz_iff [DecidableEq ι] :
    CesaroBounded (univ : Finset ι) (fun _ => 1) D.β ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro hB
    by_contra hD
    simp only [not_forall] at hD
    obtain ⟨i, hi⟩ := hD
    -- Either `β_i` or `β_{fe i} = 1/β_i` lies outside the circle.
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hfe : 1 < ‖D.β (D.fePerm i)‖ := by
        have hmul := D.β_fePerm i
        have : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by rw [← norm_mul, hmul, norm_one]
        have hpos : 0 < ‖D.β i‖ := norm_pos_iff.mpr (D.β_ne_zero i)
        nlinarith
      exact not_cesaroBounded_of_one_lt_norm univ _ D.β (fun _ _ => one_pos)
        (Finset.mem_univ _) hfe hB
    · exact not_cesaroBounded_of_one_lt_norm univ _ D.β (fun _ _ => one_pos)
        (Finset.mem_univ _) hgt hB
  · intro hD
    exact cesaroBounded_of_norm_le_one _ _ _ fun i _ => (hD i).le

/-- The Lefschetz pencil is the power-sum sequence. -/
theorem lefschetzPencil_eq_powerSum (n : ℕ) :
    ∑ i ∈ (univ : Finset ι), ((fun _ => 1 : ι → ℕ) i : ℂ) * D.β i ^ n = D.powerSum n := by
  simp [CurveDatum.powerSum]

/-- **Exchange law over `𝔽_q`.** The Lefschetz pencil is bounded exactly below the quantum. -/
theorem cesaroBounded_lefschetz_iff_curveCollisionCharge_lt_two [DecidableEq ι] :
    CesaroBounded (univ : Finset ι) (fun _ => 1) D.β ↔ curveCollisionCharge D < 2 := by
  rw [cesaroBounded_lefschetz_iff]
  exact (unitary_tfae D).out 0 2

/-- **Calibration rigidity on curve data.** Every explicit statistic `∑ h(β_i)` calibrated to the
same-point weight `|f|²` on the unit circle is the Rosati pairing `∑ f(β_i) conj f(β_{refl i})`. -/
theorem explicit_eq_rosatiPairing {f h : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {0}ᶜ) (hh : DifferentiableOn ℂ h {0}ᶜ)
    (hcal : ∀ w : ℂ, ‖w‖ = 1 → h w = ((‖f w‖ ^ 2 : ℝ) : ℂ)) :
    ∑ i, h (D.β i) = ∑ i, f (D.β i) * (starRingEnd ℂ) (f (D.β (D.reflPerm i))) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eq_rosatiWeight_of_circleCalibrated hf hh hcal (D.β_ne_zero i), D.β_reflPerm]

/-! ## The golden datum -/

open Real in
/-- The golden datum `q = 5`, `β = φ, φ⁻¹` has collision charge exactly the quantum `2`. -/
theorem goldenDatum_curveCollisionCharge : curveCollisionCharge goldenDatum = 2 := by
  have hφ : 1 < goldenRatio := one_lt_goldenRatio
  have hpos : 0 < goldenRatio := goldenRatio_pos
  have hord : ∀ i : Fin 2, curveOrdinate goldenDatum i = 1 := by
    intro i
    have hβpos : ∀ x : ℝ, 0 < x → ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) = 1 := by
      intro x hx
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      exact div_self (by exact_mod_cast hx.ne')
    fin_cases i
    · exact hβpos _ hpos
    · exact hβpos _ (inv_pos.mpr hpos)
  have hne : goldenDatum.β 0 ≠ goldenDatum.β 1 := by
    show ((goldenRatio : ℝ) : ℂ) ≠ ((goldenRatio⁻¹ : ℝ) : ℂ)
    rw [Ne, Complex.ofReal_inj]
    intro h
    have : goldenRatio⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
    linarith
  have hfilter : ((univ ×ˢ univ : Finset (Fin 2 × Fin 2)).filter fun p =>
      curveOrdinate goldenDatum p.1 = curveOrdinate goldenDatum p.2 ∧
        goldenDatum.β p.1 ≠ goldenDatum.β p.2) = {(0, 1), (1, 0)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, hord,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> simp [hne, hne.symm]
  rw [curveCollisionCharge, hfilter]
  rfl

end

end GaloisForLFunctions.HilbertianExplicitFormulas
