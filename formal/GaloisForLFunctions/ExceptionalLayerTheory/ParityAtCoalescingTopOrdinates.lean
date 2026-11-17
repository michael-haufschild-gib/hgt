import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerNoGo
import GaloisForLFunctions.HTGeometry.ExponentialFilterPhaseLinearization

/-!
# Parity at coalescing top ordinates

Moving an ordinate changes its quadratic form on the half-line unit sphere by at most a
constant times its displacement. The constant depends only on depth and aperture. Comparing
both spectral extremes on this common sphere allows arbitrary positive splittings of an atom,
including splittings for which the Cauchy Gram matrix approaches a singular matrix.
-/

open Complex MeasureTheory Set Filter Topology
open RHTower RHTower.CCMParityCauchy RHTower.CCMParityTopLayer

namespace GaloisForLFunctions.ExceptionalLayerTheory

noncomputable section

private abbrev halfMeasure := volume.restrict (Ioi (0 : ℝ))

private def wave (δ r s : ℝ) : ℂ := Complex.exp (-((δ : ℂ) - I * r) * s)

private def moment (δ r : ℝ) (v : ℝ → ℝ) : ℂ :=
  ∫ s, (v s : ℂ) * wave δ r s ∂halfMeasure

private theorem wave_memLp {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    MemLp (wave δ r) 2 halfMeasure :=
  memLp_exp_neg_Ioi (p := (δ : ℂ) - I * r) (by simp [hδ])

private theorem wave_norm (δ r s : ℝ) : ‖wave δ r s‖ = Real.exp (-(δ * s)) := by
  simp [wave, Complex.norm_exp, Complex.mul_re]

private theorem wave_sub_norm (δ r t s : ℝ) :
    ‖wave δ r s - wave δ t s‖ ≤ Real.exp (-(δ * s)) * (|r - t| * |s|) := by
  have split (k : ℝ) : wave δ k s =
      Complex.exp ((-(δ * s) : ℝ) : ℂ) * Complex.exp (((k * s : ℝ) : ℂ) * I) := by
    rw [wave, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [split r, split t, ← mul_sub, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa [← sub_mul, abs_mul] using norm_cexp_phase_sub_le (r * s) (t * s)

private theorem moment_bound {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1) (r : ℝ) :
    ‖moment δ r v‖ ≤ Real.sqrt (1 / (2 * δ)) := by
  have h := norm_integral_mul_sq_le_of_memLp (hv.ofReal (K := ℂ)) (wave_memLp hδ r)
  change ‖moment δ r v‖ ^ 2 ≤ (∫ s, ‖(v s : ℂ)‖ ^ 2 ∂halfMeasure) * _ at h
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, hu, one_mul, wave_norm,
    ← Real.exp_nat_mul] at h
  have he : ∀ s : ℝ, (2 : ℕ) * -(δ * s) = -(2 * δ) * s := fun s => by push_cast; ring
  simp only [he, integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity : 0 < 2 * δ)) 0,
    mul_zero, Real.exp_zero, neg_div_neg_eq] at h
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr h

private theorem moment_sub_bound {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1) (r t : ℝ) :
    ‖moment δ r v - moment δ t v‖ ≤ |r - t| * Real.sqrt (2 / (2 * δ) ^ 3) := by
  have h2δ : 0 < 2 * δ := by positivity
  have hr := wave_memLp hδ r
  have ht := wave_memLp hδ t
  have hv' := hv.ofReal (K := ℂ)
  have hd := norm_integral_mul_sq_le_of_memLp hv' (hr.sub ht)
  have hi : (∫ s, (v s : ℂ) * (wave δ r - wave δ t) s ∂halfMeasure) =
      moment δ r v - moment δ t v := by
    simp only [Pi.sub_apply, mul_sub, moment]
    exact integral_sub (hv'.integrable_mul hr) (hv'.integrable_mul ht)
  change ‖∫ s, (v s : ℂ) * (wave δ r - wave δ t) s ∂halfMeasure‖ ^ 2 ≤
    (∫ s, ‖(v s : ℂ)‖ ^ 2 ∂halfMeasure) * _ at hd
  rw [hi] at hd
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, hu, one_mul] at hd
  have hm := HTGeometry.integral_sq_mul_exp_neg_mul_Ioi h2δ
  have hint : Integrable (fun s : ℝ => s ^ 2 * Real.exp (-(2 * δ * s))) halfMeasure := by
    by_contra hn
    rw [integral_undef hn] at hm
    exact (by positivity : 0 < 2 / (2 * δ) ^ 3).ne hm
  have he : (∫ s, ‖(wave δ r - wave δ t) s‖ ^ 2 ∂halfMeasure) ≤
      |r - t| ^ 2 * (2 / (2 * δ) ^ 3) := by
    rw [← hm, ← integral_const_mul]
    apply integral_mono ((memLp_two_iff_integrable_sq_norm
      (hr.sub ht).aestronglyMeasurable).mp (hr.sub ht)) (hint.const_mul _)
    intro s
    calc ‖(wave δ r - wave δ t) s‖ ^ 2
        ≤ (Real.exp (-(δ * s)) * (|r - t| * |s|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (wave_sub_norm δ r t s) 2
      _ = _ := by
        rw [mul_pow, mul_pow, sq_abs s, ← Real.exp_nat_mul]
        push_cast
        ring_nf
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hd.trans he

/-- A unit half-line source reads one atom at aperture `a` with phase `−2ra`. -/
private def reading (δ a r : ℝ) (v : ℝ → ℝ) : ℝ :=
  (Complex.exp (((-2 * r * a : ℝ) : ℂ) * I) * moment δ r v ^ 2).re

/-- Cost per unit ordinate displacement for a unit-norm source. -/
def parityTransportCost (δ a : ℝ) : ℝ :=
  2 * |a| * Real.sqrt (1 / (2 * δ)) ^ 2 +
    2 * Real.sqrt (1 / (2 * δ)) * Real.sqrt (2 / (2 * δ) ^ 3)

private theorem reading_sub_le {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1) (a r t : ℝ) :
    |reading δ a r v - reading δ a t v| ≤ parityTransportCost δ a * |r - t| := by
  let p (k : ℝ) := Complex.exp (((-2 * k * a : ℝ) : ℂ) * I)
  let w (k : ℝ) := moment δ k v
  let B := Real.sqrt (1 / (2 * δ))
  let D := Real.sqrt (2 / (2 * δ) ^ 3)
  have hw (k : ℝ) : ‖w k‖ ≤ B := moment_bound hδ hv hu k
  have hd : ‖w r - w t‖ ≤ |r - t| * D := moment_sub_bound hδ hv hu r t
  have hp : ‖p r - p t‖ ≤ 2 * |a| * |r - t| := by
    refine (norm_cexp_phase_sub_le _ _).trans_eq ?_
    rw [show -2 * r * a - -2 * t * a = (-2 * a) * (r - t) by ring, abs_mul, abs_mul]
    norm_num
  have hs : ‖w r + w t‖ ≤ 2 * B := (norm_add_le _ _).trans (by linarith [hw r, hw t])
  change |(p r * w r ^ 2).re - (p t * w t ^ 2).re| ≤ _
  rw [← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [show p r * w r ^ 2 - p t * w t ^ 2 =
      (p r - p t) * w r ^ 2 + p t * ((w r - w t) * (w r + w t)) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_pow, p, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc _ ≤ (2 * |a| * |r - t|) * B ^ 2 + (|r - t| * D) * (2 * B) :=
      add_le_add (mul_le_mul hp (pow_le_pow_left₀ (norm_nonneg _) (hw r) 2)
        (by positivity) (by positivity))
        (mul_le_mul hd hs (norm_nonneg _) (by dsimp [D]; positivity))
    _ = _ := by unfold parityTransportCost; dsimp [B, D]; ring

private theorem form_eq_sum {m : ℕ} (δ a : ℝ) (t M : Fin m → ℝ) (v : ℝ → ℝ) :
    halfLineForm δ t M (aperturePhase t a) v = ∑ j, M j * reading δ a (t j) v := by
  simp only [halfLineForm, Complex.re_sum, aperturePhase, reading, mul_assoc,
    Complex.re_ofReal_mul, halfLinePairing, moment, wave]

private theorem form_transport {m : ℕ} {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1)
    (a r : ℝ) (t M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j) :
    |halfLineForm δ t M (aperturePhase t a) v - (∑ j, M j) * reading δ a r v| ≤
      parityTransportCost δ a * ∑ j, M j * |t j - r| := by
  rw [form_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hM j)]
  exact (mul_le_mul_of_nonneg_left (reading_sub_le hδ hv hu a (t j) r) (hM j)).trans_eq
    (by ring)

private theorem form_le_unit {m : ℕ} {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ i, 0 < t i) (hm : 0 < m)
    (M θ : Fin m → ℝ) {v : ℝ → ℝ} (hv : MemLp v 2 halfMeasure)
    (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1) :
    halfLineForm δ t M θ v ≤ max (ccmLambdaMax δ t M θ) 0 := by
  obtain ⟨x, hp, hn⟩ := exists_realProfile_projection hδ ht htpos hv
  rw [← halfLineForm_congr M θ hp, ← quadForm_eq_halfLineForm hδ]
  rw [hu] at hn
  calc _ ≤ ccmLambdaMax δ t M θ * normForm δ t x :=
        quadForm_le_lambdaMax_mul hδ ht htpos hm M θ x
    _ ≤ max (ccmLambdaMax δ t M θ) 0 * 1 :=
        mul_le_mul (le_max_left _ _) hn (normForm_nonneg hδ t x) (le_max_right _ _)
    _ = _ := mul_one _

private def singletonHeight (r : ℝ) : Fin 1 → ℝ := fun _ => r

private theorem singleton_form (δ a r : ℝ) (v : ℝ → ℝ) :
    halfLineForm δ (singletonHeight r) 1 (aperturePhase (singletonHeight r) a) v =
      reading δ a r v := by simp [form_eq_sum, singletonHeight]

/-- The strict singleton gap survives any splitting whose total displacement cost, counted
with multiplicity, is less than half the gap times the total mass. -/
theorem parityBalance_pos_of_transport {m : ℕ} {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (a : ℝ) {t M : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j)
    (hm : 0 < m) (hM : ∀ j, 0 < M j)
    (hgap : 2 * (parityTransportCost δ a * ∑ j, M j * |t j - r|) <
      (∑ j, M j) * (ccmLambdaMax δ (fun _ : Fin 1 => r) 1 (fun _ => -2 * r * a) -
        max (ccmLambdaMax δ (fun _ : Fin 1 => r) 1 (halfTurn (fun _ => -2 * r * a))) 0)) :
    0 < ccmParityBalance δ t M (aperturePhase t a) := by
  let s := singletonHeight r
  let φ := aperturePhase s a
  let θ := aperturePhase t a
  let L := ccmLambdaMax δ s 1 φ
  let B := max (ccmLambdaMax δ s 1 (halfTurn φ)) 0
  let W := ∑ j, M j
  let E := parityTransportCost δ a * ∑ j, M j * |t j - r|
  have hs : Function.Injective s := fun _ _ _ => Subsingleton.elim _ _
  have hspos : ∀ i, 0 < s i := fun _ => hr
  have hW : 0 ≤ W := Finset.sum_nonneg fun j _ => (hM j).le
  have hE : 0 ≤ E := by
    dsimp [E, parityTransportCost]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
      mul_nonneg (hM j).le (abs_nonneg _))
  change 2 * E < W * (L - B) at hgap
  -- A singleton maximizing profile tests the split operator from below.
  obtain ⟨x, hx, hxmax, -⟩ := exists_isMaxOn_quadForm hδ hs hspos (by decide) 1 φ
  let v := realProfile δ s x
  have hv := memLp_realProfile hδ s x
  have hv1 : ∫ u, v u ^ 2 ∂halfMeasure = 1 := (normForm_eq_integral hδ s x).symm.trans hx
  have hvL : reading δ a r v = L :=
    (singleton_form δ a r v).symm.trans ((quadForm_eq_halfLineForm hδ s 1 φ x).symm.trans hxmax)
  have hvE := (abs_le.mp (form_transport hδ hv hv1 a r t M fun j => (hM j).le)).1
  rw [hvL] at hvE
  have hlow : W * L - E ≤ max (ccmLambdaMax δ t M θ) 0 := by
    have hle := form_le_unit hδ ht htpos hm M θ hv hv1
    change -E ≤ halfLineForm δ t M θ v - W * L at hvE
    linarith only [hle, hvE]
  -- The maximizing profile of the reflected split operator tests the singleton floor.
  obtain ⟨y, hy, hymax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M (halfTurn θ)
  let u := realProfile δ t y
  have hum := memLp_realProfile hδ t y
  have hu1 : ∫ z, u z ^ 2 ∂halfMeasure = 1 := (normForm_eq_integral hδ t y).symm.trans hy
  have huQ : halfLineForm δ t M θ u = -ccmLambdaMax δ t M (halfTurn θ) := by
    change halfLineForm δ t M θ (realProfile δ t y) = _
    rw [← quadForm_eq_halfLineForm hδ, ← hymax, quadForm_halfTurn, neg_neg]
  have huB := halfLineForm_ge hδ hs hspos (by decide) 1 φ hum
  change -(B * (∫ z, u z ^ 2 ∂halfMeasure)) ≤ halfLineForm δ s 1 φ u at huB
  rw [hu1, mul_one, singleton_form] at huB
  have huE := (abs_le.mp (form_transport hδ hum hu1 a r t M fun j => (hM j).le)).1
  rw [huQ] at huE
  change -E ≤ -ccmLambdaMax δ t M (halfTurn θ) - W * reading δ a r u at huE
  have hWB := mul_le_mul_of_nonneg_left huB hW
  have hupper : ccmLambdaMax δ t M (halfTurn θ) ≤ W * B + E := by linarith only [hWB, huE]
  have hB : 0 ≤ B := le_max_right _ _
  have hpos : 0 < W * L - E := by
    rw [mul_sub] at hgap
    linarith only [hgap, hE, mul_nonneg hW hB]
  have htop : 0 < ccmLambdaMax δ t M θ := (lt_max_iff.mp (hpos.trans_le hlow)).resolve_right
    (lt_irrefl _)
  rw [max_eq_left htop.le] at hlow
  change 0 < ccmLambdaMax δ t M θ - ccmLambdaMax δ t M (halfTurn θ)
  rw [mul_sub] at hgap
  linarith only [hgap, hlow, hupper]

/-- At every positive depth and height, a common aperture has positive balance for every
finite layer with sufficiently small multiplicity-weighted mean distance to that height. -/
theorem exists_aperture_positive_of_concentrated_ordinates {δ r : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) : ∃ a ε : ℝ, 0 < ε ∧ ∀ {m : ℕ} (t M : Fin m → ℝ),
      Function.Injective t → (∀ j, 0 < t j) → 0 < m → (∀ j, 0 < M j) →
      (∑ j, M j * |t j - r|) < ε * ∑ j, M j →
      0 < ccmParityBalance δ t M (aperturePhase t a) := by
  let s := singletonHeight r
  have hs : Function.Injective s := fun _ _ _ => Subsingleton.elim _ _
  have hpos : ∀ j, 0 < s j := fun _ => hr
  obtain ⟨a, -, hF⟩ := ccm_exists_large_aperture_odd_wins (m := 1) hδ hs hpos
    (M := 1) (fun _ => zero_lt_one) (by decide) (fun k hk hsum => hk (by
      have hz : (k 0 : ℝ) * r = 0 := by simpa [s, singletonHeight] using hsum
      have hk0 : k 0 = 0 := by exact_mod_cast (mul_eq_zero.mp hz).resolve_right hr.ne'
      funext i
      simpa [Subsingleton.elim i 0] using hk0)) 0
  let L := ccmLambdaMax δ s 1 (aperturePhase s a)
  let B := max (ccmLambdaMax δ s 1 (halfTurn (aperturePhase s a))) 0
  have hBL : B < L := max_lambdaMax_halfTurn_lt_of_balance_pos hδ hs hpos (by decide) 1 _ hF
  let K := parityTransportCost δ a
  have hK : 0 < K := by dsimp [K, parityTransportCost]; positivity
  let ε := (L - B) / (2 * K)
  have hε : 0 < ε := div_pos (sub_pos.mpr hBL) (by positivity)
  refine ⟨a, ε, hε, fun t M ht htpos hm hM hnear => ?_⟩
  apply parityBalance_pos_of_transport hδ hr a ht htpos hm hM
  have h := mul_lt_mul_of_pos_left hnear (by positivity : 0 < 2 * K)
  have hcancel : 2 * K * ε = L - B := by
    dsimp [ε]; field_simp
  change 2 * (K * _) < _ * (L - B)
  rw [← mul_assoc (2 * K) ε, hcancel, mul_comm (L - B)] at h
  simpa only [mul_assoc] using h

/-- A concentrated finite top layer forces reflection-odd restricted Weil ground states at
arbitrarily large apertures, for all multiplicities and all integer relations. -/
theorem concentrated_top_ordinates_force_odd_ground {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {m : ℕ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t),
      (∑ j, h.mult j * |t j - r|) < ε * ∑ j, h.mult j →
      ∀ A : ℝ, ∃ a : SuzukiPositiveAperture, A < a.1 ∧ ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
          ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
          ccmArchimedeanFormReflection a u = -u := by
  obtain ⟨a, ε, hε, hpos⟩ := exists_aperture_positive_of_concentrated_ordinates hδ hr
  exact ⟨ε, hε, fun h hnear => exists_aperture_ground_odd h
    ⟨a, hpos _ _ h.injective h.t_pos h.nonempty h.mult_pos hnear⟩⟩

end

end GaloisForLFunctions.ExceptionalLayerTheory
