import GaloisForLFunctions.RHTower.CCMRestrictedWeilApertureMonotonicity
import GaloisForLFunctions.RHTower.CCMConnesConsaniHilbertOne

/-!
# Aperture families of bounded remainders and their ground energies

The literal restricted Weil form at aperture `a` is `⟪u,u⟫ + ⟪B_a J_a u, J_a u⟫` on the archimedean
form domain, with `J_a` the compact embedding into the aperture Hilbert space and `B_a` a bounded
self-adjoint remainder.  Everything about its ground energy that does not depend on the arithmetic
content of `B_a` — the Rayleigh bound, the existence of a ground form state, the scaling law, the
norm–mass bound, the closedness of sublevel sets, and monotonicity in the aperture — is proved here
once for an arbitrary family `a ↦ B_a` satisfying the single aperture-compatibility law:
extending a form vector to a larger aperture does not change the remainder pairing.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A family of bounded self-adjoint remainders on the aperture Hilbert spaces, compatible with
aperture extension of form vectors. -/
structure CCMRemainderFamily where
  B : ∀ a : SuzukiPositiveAperture, suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a
  selfAdjoint : ∀ a, IsSelfAdjoint (B a)
  compat : ∀ {a b : SuzukiPositiveAperture}, a.1 ≤ b.1 →
    ∀ {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}, v.1 = u.1 →
      (inner ℂ (B b (ccmArchimedeanFormToAperture b v)) (ccmArchimedeanFormToAperture b v)).re =
        (inner ℂ (B a (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a u)).re

namespace CCMRemainderFamily

variable (F : CCMRemainderFamily)

/-- The remainder pairing on the aperture Hilbert space. -/
def diagonal (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  (inner ℂ (F.B a f) f).re

theorem continuous_diagonal (a : SuzukiPositiveAperture) : Continuous (F.diagonal a) := by
  unfold diagonal
  exact Complex.continuous_re.comp ((F.B a).continuous.inner continuous_id)

/-- The quadratic form of the family on the archimedean form domain. -/
def Q (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  ‖u‖ ^ 2 + F.diagonal a (ccmArchimedeanFormToAperture a u)

theorem continuous_Q (a : SuzukiPositiveAperture) : Continuous (F.Q a) := by
  unfold Q
  exact (continuous_norm.pow 2).add
    ((F.continuous_diagonal a).comp (ccmArchimedeanFormToAperture a).continuous)

theorem re_inner_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : H) :
    (inner ℂ u u).re = ‖u‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  simp [pow_two, Complex.mul_re]

theorem Q_eq_form_re (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    F.Q a u = (inner ℂ u u +
      inner ℂ (F.B a (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a u)).re := by
  unfold Q diagonal
  rw [Complex.add_re, re_inner_self]

/-- The ground energy of the family at aperture `a`, through the Friedrichs covariance. -/
def energy (a : SuzukiPositiveAperture) : ℝ :=
  ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (F.B a) (F.selfAdjoint a)‖⁻¹ -
    boundedPerturbedFormShift (F.B a)

/-- The Friedrichs operator of the family at aperture `a`. -/
def operator (a : SuzukiPositiveAperture) : suzukiApertureHilbert a →ₗ.[ℂ] suzukiApertureHilbert a :=
  boundedPerturbedFriedrichsOperator (ccmArchimedeanFormToAperture a) (F.B a) (F.selfAdjoint a)

theorem energy_mul_formNorm_sq_le (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    F.energy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ F.Q a u := by
  have h := boundedPerturbedForm_ground_mul_norm_sq_le (ccmArchimedeanFormToAperture a) (F.B a)
    (F.selfAdjoint a) (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a) u
  rw [Q_eq_form_re]
  exact h

theorem abs_re_inner_apply_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (f : H) : |(inner ℂ (T f) f).re| ≤ ‖T‖ * ‖f‖ ^ 2 := by
  calc |(inner ℂ (T f) f).re| ≤ ‖inner ℂ (T f) f‖ := Complex.abs_re_le_norm _
    _ ≤ ‖T f‖ * ‖f‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖f‖) * ‖f‖ := mul_le_mul_of_nonneg_right (T.le_opNorm f) (norm_nonneg _)
    _ = ‖T‖ * ‖f‖ ^ 2 := by ring

theorem norm_sq_le_Q_add (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ‖u‖ ^ 2 ≤ F.Q a u + ‖F.B a‖ * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  unfold Q
  have habs := abs_re_inner_apply_le (F.B a) (ccmArchimedeanFormToAperture a u)
  have := neg_abs_le (inner ℂ (F.B a (ccmArchimedeanFormToAperture a u))
    (ccmArchimedeanFormToAperture a u)).re
  unfold diagonal
  linarith

theorem Q_smul (a : SuzukiPositiveAperture) (c : ℂ) (u : CCMArchimedeanFormDomain a) :
    F.Q a (c • u) = ‖c‖ ^ 2 * F.Q a u := by
  rw [Q_eq_form_re, Q_eq_form_re, map_smul, map_smul]
  rw [inner_smul_left u (c • u) c, inner_smul_right u u c,
    inner_smul_left (F.B a (ccmArchimedeanFormToAperture a u))
      (c • ccmArchimedeanFormToAperture a u) c,
    inner_smul_right (F.B a (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u) c]
  rw [← mul_add, ← mul_add, ← mul_assoc]
  have hc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-! ## Existence of a ground form state -/

theorem exists_groundFormState (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
        F.Q a u = F.energy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  set J := ccmArchimedeanFormToAperture a with hJ
  set B := F.B a with hB
  have hBsa := F.selfAdjoint a
  have hJinj := ccmArchimedeanFormToAperture_injective a
  have hDense := denseRange_ccmArchimedeanFormToAperture a
  set C := boundedPerturbedFormCovariance J B hBsa with hC
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B hBsa hJinj hDense
  obtain ⟨e, hene, he⟩ := boundedPerturbedFormCovariance_exists_norm_eigenvector J B hBsa hJinj
    hDense (isCompactOperator_ccmArchimedeanFormToAperture a)
  set mu : ℝ := ‖C‖ with hmu_def
  change C e = (mu : ℂ) • e at he
  have hmu0 : mu ≠ 0 := by
    intro h0
    apply hene
    apply hCinj
    rw [he, h0, map_zero]
    simp
  have hmuC : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu0
  set z : suzukiApertureHilbert a := (mu : ℂ)⁻¹ • e with hz
  have hCz : C z = e := by
    rw [hz, map_smul, he, smul_smul, inv_mul_cancel₀ hmuC, one_smul]
  -- the representation identity at `y = z`
  have hrep := boundedPerturbedFriedrichsOperator_represents_form J B hBsa hJinj hDense z
  set u : CCMArchimedeanFormDomain a :=
    boundedPerturbedFormRieszInv J B hBsa (J.adjoint z) with hu
  have hJu : J u = e := by
    have : C z = J u := rfl
    rw [← this, hCz]
  refine ⟨u, by rw [hJu]; exact hene, ?_⟩
  -- the Friedrichs operator acts on `e` by the ground energy
  have hedom : e ∈ (closedDenseInverse C).domain := by
    rw [closedDenseInverse_domain]
    exact ⟨z, hCz⟩
  have hinv : closedDenseInverse C ⟨e, hedom⟩ = z := by
    have h := (closedDenseInverse_apply_C C hCinj z).2
    have heq : (⟨e, hedom⟩ : (closedDenseInverse C).domain) =
        ⟨C z, (closedDenseInverse_apply_C C hCinj z).1⟩ := Subtype.ext hCz.symm
    rw [heq]
    exact h
  have hrep' := hrep u
  dsimp only at hrep'
  obtain ⟨hxJ, hform⟩ := hrep'
  -- identify the operator value
  set x : (boundedPerturbedFriedrichsOperator J B hBsa).domain :=
    ⟨C z, by
      change C z ∈ (closedDenseInverse C).domain
      exact (closedDenseInverse_apply_C C hCinj z).1⟩ with hx
  have hxval : (x : suzukiApertureHilbert a) = e := hCz
  have hop : boundedPerturbedFriedrichsOperator J B hBsa x = (F.energy a : ℂ) • e := by
    rw [boundedPerturbedFriedrichsOperator_apply]
    have hdomx : ((x : suzukiApertureHilbert a)) ∈ (closedDenseInverse C).domain := by
      rw [hxval]; exact hedom
    have hsub : closedDenseInverse C ⟨(x : suzukiApertureHilbert a), by
        simpa only [boundedPerturbedFriedrichsOperator_domain] using x.property⟩ = z := by
      have heq : (⟨(x : suzukiApertureHilbert a), by
          simpa only [boundedPerturbedFriedrichsOperator_domain] using x.property⟩ :
          (closedDenseInverse C).domain) = ⟨e, hedom⟩ := Subtype.ext hxval
      rw [heq, hinv]
    rw [hsub, hxval, hz]
    unfold energy
    rw [← hC, ← hmu_def]
    push_cast
    module
  -- take real parts of the form identity
  rw [Q_eq_form_re]
  have hform' : inner ℂ (boundedPerturbedFriedrichsOperator J B hBsa x) (J u) =
      inner ℂ u u + inner ℂ (B (J u)) (J u) := hform
  rw [← hform', hop, hJu, inner_smul_left e e (F.energy a : ℂ), Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  exact re_inner_self e

/-! ## Aperture compatibility and monotonicity -/

theorem Q_eq_of_val_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    F.Q b v = F.Q a u := by
  unfold Q diagonal
  rw [F.compat hab hvu]
  have hnorm : ‖v‖ = ‖u‖ := by
    change ‖v.1‖ = ‖u.1‖
    rw [hvu]
  rw [hnorm]

theorem energy_antitone {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    F.energy b ≤ F.energy a := by
  obtain ⟨u, huNe, huGround⟩ := F.exists_groundFormState a
  obtain ⟨v, hvu⟩ := exists_ccmArchimedeanFormDomain_extension hab u
  have hfloor := F.energy_mul_formNorm_sq_le b v
  rw [F.Q_eq_of_val_eq hab hvu, huGround, norm_ccmArchimedeanFormToAperture_eq_of_val_eq hvu]
    at hfloor
  have hnormPos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr huNe)
  exact le_of_mul_le_mul_right hfloor hnormPos

theorem antitone_energy : Antitone F.energy := fun _ _ hab => F.energy_antitone hab

/-! ## Closed sublevel sets -/

theorem isClosed_sublevel (a : SuzukiPositiveAperture) (c : ℝ) :
    IsClosed {f : suzukiApertureHilbert a |
      ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f ∧ F.Q a u ≤ c} := by
  rw [← isSeqClosed_iff_isClosed]
  intro x f hx hxf
  choose u huJ huQ using hx
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto x hxf)
  have hMx (n : ℕ) : ‖x n‖ ≤ M := hM (x n) ⟨n, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg (x 0)).trans (hMx 0)
  let D : ℝ := max 0 (c + ‖F.B a‖ * M ^ 2)
  have hD0 : 0 ≤ D := le_max_left _ _
  have huNormSq (n : ℕ) : ‖u n‖ ^ 2 ≤ D := by
    apply (F.norm_sq_le_Q_add a (u n)).trans
    rw [huJ n]
    apply le_max_of_le_right
    have hxSq : ‖x n‖ ^ 2 ≤ M ^ 2 := by nlinarith [hMx n, norm_nonneg (x n)]
    have hmul := mul_le_mul_of_nonneg_left hxSq (norm_nonneg (F.B a))
    linarith [huQ n]
  have huNorm (n : ℕ) : ‖u n‖ ≤ Real.sqrt D := by
    nlinarith [huNormSq n, Real.sq_sqrt hD0, norm_nonneg (u n), Real.sqrt_nonneg D]
  have huEnorm : ∀ᶠ n in atTop, ‖u n‖ₑ ≤ ENNReal.ofReal (Real.sqrt D) := by
    filter_upwards with n
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (huNorm n)
  obtain ⟨v, hvJ, -⟩ := exists_ccmArchimedeanFormDomain_norm_enorm_le_of_tendsto a u f
    (by simpa only [huJ] using hxf) (ENNReal.ofReal (Real.sqrt D)) (by simp) huEnorm
  refine ⟨v, hvJ, ?_⟩
  by_contra hvc
  have hcv : c < F.Q a v := lt_of_not_ge hvc
  let delta : ℝ := (F.Q a v - c) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hbTendsto : Tendsto (fun n => F.diagonal a (x n)) atTop (nhds (F.diagonal a f)) :=
    ((F.continuous_diagonal a).tendsto f).comp hxf
  have hbEventually : ∀ᶠ n in atTop, F.diagonal a f - delta < F.diagonal a (x n) :=
    hbTendsto.eventually (Ioi_mem_nhds (by linarith))
  let E : ℝ := ‖v‖ ^ 2 - delta
  have huTightSq : ∀ᶠ n in atTop, ‖u n‖ ^ 2 ≤ E := by
    filter_upwards [hbEventually] with n hbn
    have huQn : ‖u n‖ ^ 2 + F.diagonal a (x n) ≤ c := by
      have : F.Q a (u n) = ‖u n‖ ^ 2 + F.diagonal a (x n) := by
        unfold Q; rw [huJ n]
      linarith [huQ n]
    have hvdecomp : F.Q a v = ‖v‖ ^ 2 + F.diagonal a f := by
      unfold Q; rw [hvJ]
    have hdeltaEq : delta = (‖v‖ ^ 2 + F.diagonal a f - c) / 2 := by
      show (F.Q a v - c) / 2 = _
      rw [hvdecomp]
    show ‖u n‖ ^ 2 ≤ ‖v‖ ^ 2 - delta
    rw [hdeltaEq] at hbn ⊢
    nlinarith [huQn]
  have hE0 : 0 ≤ E := by
    obtain ⟨n, hn⟩ := huTightSq.exists
    exact (sq_nonneg ‖u n‖).trans hn
  have huTight : ∀ᶠ n in atTop, ‖u n‖ ≤ Real.sqrt E := by
    filter_upwards [huTightSq] with n hn
    nlinarith [Real.sq_sqrt hE0, norm_nonneg (u n), Real.sqrt_nonneg E]
  have huTightEnorm : ∀ᶠ n in atTop, ‖u n‖ₑ ≤ ENNReal.ofReal (Real.sqrt E) := by
    filter_upwards [huTight] with n hn
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hn
  obtain ⟨w, hwJ, hwNorm⟩ := exists_ccmArchimedeanFormDomain_norm_enorm_le_of_tendsto a u f
    (by simpa only [huJ] using hxf) (ENNReal.ofReal (Real.sqrt E)) (by simp) huTightEnorm
  have hwv : w = v := ccmArchimedeanFormToAperture_injective a (hwJ.trans hvJ.symm)
  subst hwv
  have hwNorm' : ‖w‖ ≤ Real.sqrt E := by
    have h := hwNorm
    rw [← ofReal_norm] at h
    exact ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg E) |>.mp h
  have hsq : ‖w‖ ^ 2 ≤ E := by
    calc ‖w‖ ^ 2 ≤ (Real.sqrt E) ^ 2 := by gcongr
      _ = E := Real.sq_sqrt hE0
  have hE : E = ‖w‖ ^ 2 - delta := rfl
  rw [hE] at hsq
  linarith

end CCMRemainderFamily

end RHTower

end
