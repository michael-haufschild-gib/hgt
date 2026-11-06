import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheOuterPredictorReplacesTheGroundState
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.EveryCriticalRatioIsPositiveOnALargerWindow
import GaloisForLFunctions.GrowingWindowsOfSpecZ.AWindowIsTheUnionOfItsLattices

/-!
# Passivity certified from arithmetic data

The Weil form is positive on windows of length up to `A₀ = 2·successorWeilFloorAperture`, past `log 2`, unconditionally. So on these windows the causal certificate is a theorem about `Spec ℤ`, with primes in it.

* **Outer predictors exist** (`exists_outer_predictor_of_certified`). Every lattice window of a nonzero bump of total length at most `A₀` has an outer predictor with positive margin.
* **A Riemann hypothesis on each certified window** (`paraPoly_zero_on_circle_of_certified`). The self-reciprocal polynomials of the Weil lattice have all zeros on the unit circle.
* **Each echo lies in its Schur band** (`abs_schurParam_lt_of_certified`). This includes the echoes that carry `Λ(2)`.

**One critical ratio.** At a ratio `R` below the threshold of a window, in particular below `R₀` for every window, the pencil `a_φ Q(H) + (7J(1)/R) M₈(H)` is positive. The term `M₈` is an exponentially tilted slack, which breaks translation
invariance, and the form on a lattice is no longer Toeplitz. The certificate survives as a triangular sum of squares with positive pivots (`exists_causal_certificate`, `exists_certificate_at_critical_ratio`): causality needs no Toeplitz structure, only the Levinson recursion does.
The tilt also makes the left tail tight (`integral_tail_le_exponentialMass`).
-/

open Finset Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis
  CohomologyOfWindowsOfSpecZ ArithmeticHodgeTheoryOfDegenerations WindowTowerOfSpecZ
  ArithmeticIncidencePositivity

noncomputable section

/-- The certified aperture: Weil's form is positive on windows of this length. -/
def certifiedAperture : ℝ := 2 * successorWeilFloorAperture

/-- **Weil's form is positive on certified windows.** -/
theorem weilQuad_pos_of_certified {A : ℝ} (hA : A ≤ certifiedAperture) {G : ℝ → ℝ}
    (hG : IsWindowTest A G) (hG0 : G ≠ 0) : 0 < weilQuad G := by
  have hfloor := weilQuad_ge_of_le_two_mul_successorWeilFloorAperture hA hG
  have hm := mem_realTests_of_isWindowTest hG
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hG0
  have hc : Continuous G := ContDiff.continuous hm.1
  have hcs : HasCompactSupport G := hm.2
  have hcs2 : HasCompactSupport fun u => G u ^ 2 := hcs.mono fun u hu h0 => hu (by simp [h0])
  have hpos : 0 < ∫ u, G u ^ 2 :=
    (hc.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero hcs2 (fun _ => sq_nonneg _)
      (x := x) (pow_ne_zero 2 hx)
  linarith

/-- Lattice windows of certified length are positive definite. -/
theorem toeplitzPosDef_of_certified {A : ℝ} (hA : A ≤ certifiedAperture) {φ : ℝ → ℝ} {r : ℝ}
    (hφ : IsWindowTest r φ) (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) {n : ℕ} (hlen : n * h + r ≤ A) :
    ToeplitzPosDef (weilSeq φ h) (n + 1) :=
  (toeplitzForm_posDef_iff (weilSeq_isEven φ h) n).mpr
    (window_pos_iff_lattices.mp (fun _ hG hG0 => weilQuad_pos_of_certified hA hG hG0) φ r hφ hφ0 h hh n hlen)

/-- **Outer predictors exist on certified windows.** -/
theorem exists_outer_predictor_of_certified {A : ℝ} (hA : A ≤ certifiedAperture) {φ : ℝ → ℝ} {r : ℝ}
    (hφ : IsWindowTest r φ) (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) {n : ℕ} (hlen : n * h + r ≤ A) :
    ∃ a : Fin n → ℝ, IsPredictor (weilSeq φ h) n a ∧ 0 < predErr (weilSeq φ h) n a ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0 :=
  (toeplitzPosDef_iff_exists_outer_predictor (weilSeq_isEven φ h) n).mp
    (toeplitzPosDef_of_certified hA hφ hφ0 hh hlen)

/-- **A Riemann hypothesis on each certified window.** -/
theorem paraPoly_zero_on_circle_of_certified {A : ℝ} (hA : A ≤ certifiedAperture) {φ : ℝ → ℝ} {r : ℝ}
    (hφ : IsWindowTest r φ) (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) {n : ℕ} (hlen : n * h + r ≤ A)
    {ε : ℝ} (hε : ε ^ 2 = 1) {z : ℂ} (hz : paraPoly (levinsonPred (weilSeq φ h) n) ε z = 0) : ‖z‖ = 1 :=
  paraPoly_zero_on_circle
    (predPoly_levinson_ne_zero (weilSeq_isEven φ h) n (toeplitzPosDef_of_certified hA hφ hφ0 hh hlen)) hε hz

/-- **Each echo lies in its Schur band** on certified windows. -/
theorem abs_schurParam_lt_of_certified {A : ℝ} (hA : A ≤ certifiedAperture) {φ : ℝ → ℝ} {r : ℝ}
    (hφ : IsWindowTest r φ) (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) {n : ℕ}
    (hlen : ((n + 1 : ℕ) : ℝ) * h + r ≤ A) :
    |schurParam (weilSeq φ h) n| < levinsonErr (weilSeq φ h) n := by
  have hlen' : (n : ℝ) * h + r ≤ A := by
    push_cast at hlen
    nlinarith
  exact (posDef_succ_iff_abs_schur_lt (weilSeq_isEven φ h)
    (toeplitzPosDef_of_certified hA hφ hφ0 hh hlen')).mp
    (toeplitzPosDef_of_certified hA hφ hφ0 hh hlen)

/-! ### The causal certificate without Toeplitz structure -/

/-- **The causal certificate of a positive form.** A positive definite symmetric form is a sum of squares with positive pivots and unit-triangular rows. -/
theorem exists_causal_certificate :
    ∀ (n : ℕ) (B : Fin n → Fin n → ℝ), (∀ i j, B i j = B j i) →
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i, ∑ j, B i j * x i * x j) →
      ∃ (p : Fin n → ℝ) (v : Fin n → Fin n → ℝ), (∀ m, 0 < p m) ∧ (∀ m, v m m = 1) ∧
        (∀ m i, i < m → v m i = 0) ∧
        ∀ x : Fin n → ℝ, ∑ i, ∑ j, B i j * x i * x j = ∑ m, p m * (∑ i, v m i * x i) ^ 2
  | 0, _, _, _ => ⟨fun m => m.elim0, fun m => m.elim0, fun m => m.elim0, fun m => m.elim0,
      fun x => by simp⟩
  | n + 1, B, hsym, hpos => by
    have hexp : ∀ (x₀ : ℝ) (y : Fin n → ℝ), ∑ i, ∑ j, B i j * (Fin.cons x₀ y : Fin (n + 1) → ℝ) i *
        (Fin.cons x₀ y : Fin (n + 1) → ℝ) j = B 0 0 * x₀ ^ 2 +
          2 * x₀ * ∑ j : Fin n, B 0 j.succ * y j + ∑ i : Fin n, ∑ j : Fin n, B i.succ j.succ * y i * y j := by
      intro x₀ y
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib]
      have e : ∑ i : Fin n, B i.succ 0 * y i * x₀ = x₀ * ∑ j : Fin n, B 0 j.succ * y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsym]
        ring
      have e2 : ∑ j : Fin n, B 0 j.succ * x₀ * y j = x₀ * ∑ j : Fin n, B 0 j.succ * y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, e2]
      ring
    have ha : 0 < B 0 0 := by
      have h := hpos (Fin.cons 1 0) (fun h0 => by simpa using congrFun h0 0)
      rw [hexp] at h
      simpa using h
    set c : Fin n → ℝ := fun j => B 0 j.succ / B 0 0 with hc
    set S : Fin n → Fin n → ℝ := fun i j => B i.succ j.succ - B 0 0 * c i * c j with hS
    have hid : ∀ (x₀ : ℝ) (y : Fin n → ℝ), ∑ i, ∑ j, B i j * (Fin.cons x₀ y : Fin (n + 1) → ℝ) i *
        (Fin.cons x₀ y : Fin (n + 1) → ℝ) j =
          B 0 0 * (x₀ + ∑ j, c j * y j) ^ 2 + ∑ i, ∑ j, S i j * y i * y j := by
      intro x₀ y
      rw [hexp]
      have hL : ∑ j : Fin n, B 0 j.succ * y j = B 0 0 * ∑ j, c j * y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hc]
        field_simp
      have hLL : (∑ j, c j * y j) ^ 2 = ∑ i, ∑ j, c i * c j * y i * y j := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have hSS : ∑ i, ∑ j, S i j * y i * y j = ∑ i : Fin n, ∑ j : Fin n, B i.succ j.succ * y i * y j -
          B 0 0 * (∑ j, c j * y j) ^ 2 := by
        rw [hLL, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hS]
        ring
      rw [hL, hSS]
      ring
    have hSsym : ∀ i j, S i j = S j i := fun i j => by
      simp only [hS]
      rw [hsym]
      ring
    have hSpos : ∀ y : Fin n → ℝ, y ≠ 0 → 0 < ∑ i, ∑ j, S i j * y i * y j := fun y hy => by
      have hne : (Fin.cons (-∑ j, c j * y j) y : Fin (n + 1) → ℝ) ≠ 0 := by
        intro h0
        apply hy
        funext j
        simpa using congrFun h0 j.succ
      have h := hpos _ hne
      rw [hid] at h
      simpa using h
    obtain ⟨p', v', hp', hv1, hv0, hsum⟩ := exists_causal_certificate n S hSsym hSpos
    refine ⟨Fin.cons (B 0 0) p', Fin.cons (Fin.cons 1 c) fun m => Fin.cons 0 (v' m), ?_, ?_, ?_, ?_⟩
    · intro m
      refine Fin.cases ?_ (fun m => ?_) m
      · simpa using ha
      · simpa using hp' m
    · intro m
      refine Fin.cases ?_ (fun m => ?_) m
      · simp
      · simpa using hv1 m
    · intro m i hi
      refine Fin.cases (fun hi => absurd hi (Fin.not_lt_zero _)) (fun m => ?_) m hi
      intro hi'
      refine Fin.cases ?_ (fun i => ?_) i hi'
      · intro _
        simp
      · intro hi2
        simpa using hv0 m i (Fin.succ_lt_succ_iff.mp hi2)
    · intro x
      have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
      conv_lhs => rw [hx]
      rw [hid, hsum, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      congr 1
      · congr 2
        rw [Fin.sum_univ_succ]
        simp [Fin.tail]
      · refine Finset.sum_congr rfl fun m _ => ?_
        congr 2
        rw [Fin.sum_univ_succ]
        simp [Fin.tail]

/-! ### One critical ratio -/

/-- The pencil at ratio `R` on the lattice sites `i, j`. -/
def pencilMatrix (R : ℝ) (φ : ℝ → ℝ) (h : ℝ) {n : ℕ} (i j : Fin n) : ℝ :=
  splineAtom * weilSeq φ h ((i : ℤ) - j) +
    7 * tiltedJordanOne / R * ∫ u, Real.exp (-(8 * u)) * (φ (u + (i : ℕ) * h) * φ (u + (j : ℕ) * h))

/-- The pencil of a lattice test is the quadratic form of the pencil matrix. -/
theorem windowPencil_latticeTest (R : ℝ) {φ : ℝ → ℝ} (hφ : φ ∈ realTests) (h : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    windowPencil R (latticeTest φ h x) = ∑ i, ∑ j, pencilMatrix R φ h i j * x i * x j := by
  have hc : Continuous φ := ContDiff.continuous hφ.1
  have hcs : HasCompactSupport φ := hφ.2
  have hint : ∀ i j : Fin n, Integrable fun u : ℝ =>
      Real.exp (-(8 * u)) * (φ (u + (i : ℕ) * h) * φ (u + (j : ℕ) * h)) := fun i j => by
    have h1 : Continuous fun u : ℝ =>
        Real.exp (-(8 * u)) * (φ (u + (i : ℕ) * h) * φ (u + (j : ℕ) * h)) := by fun_prop
    refine h1.integrable_of_hasCompactSupport ?_
    have h2 : HasCompactSupport fun u : ℝ => φ (u + (i : ℕ) * h) :=
      hcs.comp_homeomorph (Homeomorph.addRight (((i : ℕ) : ℝ) * h))
    exact (h2.mul_right).mul_left
  have hM : exponentialMass 8 (latticeTest φ h x) = ∑ i, ∑ j, x i * x j *
      ∫ u, Real.exp (-(8 * u)) * (φ (u + (i : ℕ) * h) * φ (u + (j : ℕ) * h)) := by
    rw [exponentialMass]
    have e : ∀ u : ℝ, Real.exp (-(8 * u)) * latticeTest φ h x u ^ 2 = ∑ i, ∑ j, x i * x j *
        (Real.exp (-(8 * u)) * (φ (u + (i : ℕ) * h) * φ (u + (j : ℕ) * h))) := fun u => by
      rw [latticeTest_apply, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [e]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  rw [windowPencil, weilQuad_latticeTest hφ, hM, toeplitzForm, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pencilMatrix]
  ring

/-- **The certificate at one critical ratio.** Below the threshold of a window, every lattice of that window carries a causal certificate of the pencil. -/
theorem exists_certificate_at_critical_ratio {A R : ℝ} (hR : 0 < R)
    (hlt : (R : EReal) < windowThreshold A) {φ : ℝ → ℝ} {r : ℝ} (hφ : IsWindowTest r φ) (hφ0 : φ ≠ 0)
    {h : ℝ} (hh : 0 < h) {n : ℕ} (hlen : n * h + r ≤ A) :
    ∃ (p : Fin (n + 1) → ℝ) (v : Fin (n + 1) → Fin (n + 1) → ℝ), (∀ m, 0 < p m) ∧ (∀ m, v m m = 1) ∧
      (∀ m i, i < m → v m i = 0) ∧ ∀ x : Fin (n + 1) → ℝ,
        windowPencil R (latticeTest φ h x) = ∑ m, p m * (∑ i, v m i * x i) ^ 2 := by
  have hm := mem_realTests_of_isWindowTest hφ
  have hsym : ∀ i j : Fin (n + 1), pencilMatrix R φ h i j = pencilMatrix R φ h j i := fun i j => by
    simp only [pencilMatrix]
    have e1 : weilSeq φ h ((i : ℤ) - j) = weilSeq φ h ((j : ℤ) - i) := by
      rw [← weilSeq_isEven φ h, neg_sub]
    have e2 : (∫ u, Real.exp (-(8 * u)) * (φ (u + ((i : Fin (n + 1)) : ℕ) * h) * φ (u + ((j : Fin (n + 1)) : ℕ) * h))) =
        ∫ u, Real.exp (-(8 * u)) * (φ (u + ((j : Fin (n + 1)) : ℕ) * h) * φ (u + ((i : Fin (n + 1)) : ℕ) * h)) := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      ring
    rw [e1, e2]
  obtain ⟨p, v, hp, hv1, hv0, hsum⟩ := exists_causal_certificate (n + 1) (pencilMatrix R φ h) hsym
    fun x hx => by
      rw [← windowPencil_latticeTest R hm]
      exact pencil_pos_of_lt_windowThreshold hR hlt
        (isWindowTest_latticeTest hm hφ.vanish hh.le hlen x) (latticeTest_ne_zero hm hφ0 hh hx)
  exact ⟨p, v, hp, hv1, hv0, fun x => by rw [windowPencil_latticeTest R hm, hsum]⟩

/-- **The floor ratio works on every window.** -/
theorem exists_certificate_below_floor {R : ℝ} (hR : 0 < R) (hlt : R < apertureIndependentThreshold) {A : ℝ}
    {φ : ℝ → ℝ} {r : ℝ} (hφ : IsWindowTest r φ) (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) {n : ℕ}
    (hlen : n * h + r ≤ A) :
    ∃ (p : Fin (n + 1) → ℝ) (v : Fin (n + 1) → Fin (n + 1) → ℝ), (∀ m, 0 < p m) ∧ (∀ m, v m m = 1) ∧
      (∀ m i, i < m → v m i = 0) ∧ ∀ x : Fin (n + 1) → ℝ,
        windowPencil R (latticeTest φ h x) = ∑ m, p m * (∑ i, v m i * x i) ^ 2 :=
  exists_certificate_at_critical_ratio hR
    (lt_of_lt_of_le (by exact_mod_cast hlt) (apertureIndependentThreshold_le_windowThreshold A)) hφ hφ0 hh hlen

/-- **The tilt makes the left tail tight.** Mass below `−L` is at most `e^{−8L}` times the tilted mass. -/
theorem integral_tail_le_exponentialMass {H : ℝ → ℝ} (hH : Integrable fun u => Real.exp (-(8 * u)) * H u ^ 2)
    (hH2 : Integrable fun u => H u ^ 2) (L : ℝ) :
    ∫ u in Iic (-L), H u ^ 2 ≤ Real.exp (-(8 * L)) * exponentialMass 8 H := by
  have h1 : ∫ u in Iic (-L), H u ^ 2 ≤ ∫ u in Iic (-L), Real.exp (-(8 * L)) * (Real.exp (-(8 * u)) * H u ^ 2) := by
    refine setIntegral_mono_on hH2.integrableOn (hH.const_mul _).integrableOn measurableSet_Iic fun u hu => ?_
    have hu' : u ≤ -L := hu
    have e : Real.exp (-(8 * L)) * (Real.exp (-(8 * u)) * H u ^ 2) = Real.exp (-(8 * L) + -(8 * u)) * H u ^ 2 := by
      rw [Real.exp_add]
      ring
    rw [e]
    have h2 : (1 : ℝ) ≤ Real.exp (-(8 * L) + -(8 * u)) := Real.one_le_exp (by linarith)
    nlinarith [sq_nonneg (H u)]
  refine h1.trans ?_
  rw [integral_const_mul, exponentialMass]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact setIntegral_le_integral hH (Eventually.of_forall fun u => by positivity)

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
