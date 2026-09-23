import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRecessionConnection

/-!
# Terminal curvature recession for canonical shifted-Xi admission

This module derives arithmetic source law missing from fixed reporters.  Reciprocal-mass dilation
transports first two monic admission jets into Jacobi data with weights two and four.  Shifted
Chebyshev recession then forces exact fixed-degree terminal-curvature boundary
`y² Dₙ(y) → (4n+3)/4`, hence universal degree-normalized boundary `1/4`, positive terminal
curvature, and negative raw odd-current drift on a complete far-right chamber.

Construction is source-first and admission-sensitive: no fixed linear observation or post hoc
orientation aggregation enters.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

theorem arc_monicScale_succ {n : ℕ} (hn : 0 < n) :
    Arc.monicScale (n + 1) = Arc.monicScale n / 4 := by
  unfold Arc.monicScale XiShiftedArcsineAdmission.monicScale
  rw [show 2 * (n + 1) - 1 = (2 * n - 1) + 2 by omega, pow_add]
  norm_num
  ring

theorem arc_monicScale_pred {n : ℕ} (hn : 2 ≤ n) :
    Arc.monicScale (n - 1) = 4 * Arc.monicScale n := by
  have h := arc_monicScale_succ (n := n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at h
  linarith

theorem arc_amplitude_recurrence_one :
    X * Arc.amplitude 1 =
      Arc.amplitude 2 + (1 / 2 : ℝ) • Arc.amplitude 1 +
        (1 / 8 : ℝ) • Arc.amplitude 0 := by
  have hrec := Polynomial.Chebyshev.T_add_two ℝ (0 : ℤ)
  norm_num at hrec
  have hreccomp := congrArg (fun p : Polynomial ℝ => p.comp Arc.affine) hrec
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.X_comp,
    Polynomial.ofNat_comp] at hreccomp
  have hshape :
      (4 : ℝ) • (X * Arc.affine) =
        (Polynomial.Chebyshev.T ℝ 2).comp Arc.affine +
          (2 : ℝ) • Arc.affine + 1 := by
    have haff : Arc.affine = (2 : Polynomial ℝ) * X - 1 := rfl
    rw [haff] at hreccomp ⊢
    simp only [Polynomial.smul_eq_C_mul]
    have hone : (1 : Polynomial ℝ).comp (2 * X - 1) = 1 := by simp
    rw [hone] at hreccomp
    rw [Polynomial.C_ofNat, Polynomial.C_ofNat]
    linear_combination -hreccomp
  have hs := arc_monicScale_succ (n := 1) (by omega)
  have hp : Arc.monicScale 0 = 2 * Arc.monicScale 1 := by
    norm_num [Arc.monicScale, XiShiftedArcsineAdmission.monicScale]
  change XiShiftedArcsineAdmission.monicScale 2 =
    XiShiftedArcsineAdmission.monicScale 1 / 4 at hs
  change XiShiftedArcsineAdmission.monicScale 0 =
    2 * XiShiftedArcsineAdmission.monicScale 1 at hp
  rw [← (isUnit_iff_ne_zero.mpr (by norm_num : (8 : ℝ) ≠ 0)).smul_left_cancel]
  unfold Arc.amplitude XiShiftedArcsineAdmission.amplitude
  rw [hs, hp]
  norm_num only [Polynomial.Chebyshev.T_one, Polynomial.Chebyshev.T_zero,
    Polynomial.X_comp, Polynomial.one_comp] at hshape ⊢
  simp only [smul_add, smul_smul, mul_smul_comm]
  change (8 * Arc.monicScale 1) • (X * Arc.affine) =
    (8 * (Arc.monicScale 1 / 4)) •
        (Polynomial.Chebyshev.T ℝ 2).comp Arc.affine +
      (8 * (1 / 2 * Arc.monicScale 1)) • Arc.affine +
      (8 * (1 / 8 * (2 * Arc.monicScale 1))) • 1
  have h₂ : 8 * (Arc.monicScale 1 / 4) = 2 * Arc.monicScale 1 := by ring
  have h₄ : 8 * (1 / 2 * Arc.monicScale 1) = 4 * Arc.monicScale 1 := by ring
  have h₂' : 8 * (1 / 8 * (2 * Arc.monicScale 1)) = 2 * Arc.monicScale 1 := by ring
  rw [h₂, h₄, h₂']
  have hscaled := congrArg
    (fun p : Polynomial ℝ => (2 * Arc.monicScale 1) • p) hshape
  simp only [smul_add, smul_smul] at hscaled
  rw [show (2 * Arc.monicScale 1) * 4 = 8 * Arc.monicScale 1 by ring,
    show (2 * Arc.monicScale 1) * 2 = 4 * Arc.monicScale 1 by ring] at hscaled
  exact hscaled

theorem arc_amplitude_recurrence_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    X * Arc.amplitude n =
      Arc.amplitude (n + 1) + (1 / 2 : ℝ) • Arc.amplitude n +
        (1 / 16 : ℝ) • Arc.amplitude (n - 1) := by
  have hrec := Polynomial.Chebyshev.T_add_two ℝ ((n - 1 : ℕ) : ℤ)
  rw [show ((n - 1 : ℕ) : ℤ) + 2 = (n + 1 : ℕ) by omega,
    show ((n - 1 : ℕ) : ℤ) + 1 = n by omega] at hrec
  have hs := arc_monicScale_succ (n := n) (by omega)
  have hp := arc_monicScale_pred (n := n) hn
  have hreccomp := congrArg (fun p : Polynomial ℝ => p.comp Arc.affine) hrec
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.X_comp,
    Polynomial.ofNat_comp] at hreccomp
  have hshape :
      (4 : ℝ) • (X * (Polynomial.Chebyshev.T ℝ n).comp Arc.affine) =
        (Polynomial.Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ))).comp Arc.affine +
          (2 : ℝ) • (Polynomial.Chebyshev.T ℝ n).comp Arc.affine +
          (Polynomial.Chebyshev.T ℝ (((n - 1 : ℕ) : ℤ))).comp Arc.affine := by
    have haff : Arc.affine = (2 : Polynomial ℝ) * X - 1 := rfl
    rw [haff] at hreccomp ⊢
    simp only [Polynomial.smul_eq_C_mul]
    rw [Polynomial.C_ofNat, Polynomial.C_ofNat]
    linear_combination -hreccomp
  change XiShiftedArcsineAdmission.monicScale (n + 1) =
    XiShiftedArcsineAdmission.monicScale n / 4 at hs
  change XiShiftedArcsineAdmission.monicScale (n - 1) =
    4 * XiShiftedArcsineAdmission.monicScale n at hp
  rw [← (isUnit_iff_ne_zero.mpr (by norm_num : (16 : ℝ) ≠ 0)).smul_left_cancel]
  unfold Arc.amplitude XiShiftedArcsineAdmission.amplitude
  rw [hs, hp]
  simp only [smul_add, smul_smul, mul_smul_comm]
  change (16 * Arc.monicScale n) •
      (X * (Polynomial.Chebyshev.T ℝ n).comp Arc.affine) =
    (16 * (Arc.monicScale n / 4)) •
        (Polynomial.Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ))).comp Arc.affine +
      (16 * (1 / 2 * Arc.monicScale n)) •
        (Polynomial.Chebyshev.T ℝ n).comp Arc.affine +
      (16 * (1 / 16 * (4 * Arc.monicScale n))) •
        (Polynomial.Chebyshev.T ℝ (((n - 1 : ℕ) : ℤ))).comp Arc.affine
  have h₄ : 16 * (Arc.monicScale n / 4) = 4 * Arc.monicScale n := by ring
  have h₈ : 16 * (1 / 2 * Arc.monicScale n) = 8 * Arc.monicScale n := by ring
  have h₄' : 16 * (1 / 16 * (4 * Arc.monicScale n)) = 4 * Arc.monicScale n := by ring
  rw [h₄, h₈, h₄']
  have hscaled := congrArg
    (fun p : Polynomial ℝ => (4 * Arc.monicScale n) • p) hshape
  simp only [smul_add, smul_smul] at hscaled
  rw [show (4 * Arc.monicScale n) * 4 = 16 * Arc.monicScale n by ring,
    show (4 * Arc.monicScale n) * 2 = 8 * Arc.monicScale n by ring] at hscaled
  exact hscaled

theorem monicOrtho_normalizedCentralBinom_eq_arc_amplitude (n : ℕ) :
    HTGeometry.monicOrtho
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n =
      Arc.amplitude n := by
  cases n with
  | zero =>
      simp [Arc.amplitude, XiShiftedArcsineAdmission.amplitude,
        XiShiftedArcsineAdmission.monicScale]
  | succ n =>
      have hn : n + 1 ≠ 0 := by omega
      rw [← monicMomentAdmissionPolynomial_normalizedCentralBinom_eq_amplitude hn]
      apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
        (ne_of_gt
          (GaloisForLFunctions.HTGeometry.normalizedCentralBinom_momentHankelMatrix_det_pos
            (n + 1)))
        (HTGeometry.monicOrtho_monic _ (n + 1))
        (HTGeometry.natDegree_monicOrtho_eq _ (n + 1))
      intro i
      rw [← HTGeometry.momentInner_def, HTGeometry.momentInner_comm]
      apply HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm
        (n + 1) (n + 1) le_rfl
      rw [Polynomial.degree_X_pow]
      exact_mod_cast i.isLt

theorem monicOrthoAlpha_normalizedCentralBinom_zero :
    HTGeometry.monicOrthoAlpha
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom 0 = 1 / 2 := by
  have h := HTGeometry.monicOrthoFirstCoeff_succ
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm 0
  have hamp : (Arc.amplitude 1).coeff 0 = -1 / 2 := by
    norm_num [Arc.amplitude, XiShiftedArcsineAdmission.amplitude,
      Arc.monicScale, XiShiftedArcsineAdmission.monicScale,
      Arc.affine, XiShiftedArcsineAdmission.affine]
  rw [HTGeometry.monicOrthoFirstCoeff, HTGeometry.monicOrthoFirstCoeff,
    monicOrtho_normalizedCentralBinom_eq_arc_amplitude] at h
  simp only [hamp] at h
  linarith

theorem arc_amplitude_monic_all (n : ℕ) : (Arc.amplitude n).Monic := by
  cases n with
  | zero =>
      simp [Arc.amplitude, XiShiftedArcsineAdmission.amplitude,
        XiShiftedArcsineAdmission.monicScale]
  | succ n => exact Arc.amplitude_monic (by omega)

theorem arc_amplitude_natDegree_all (n : ℕ) : (Arc.amplitude n).natDegree = n := by
  cases n with
  | zero =>
      simp [Arc.amplitude, XiShiftedArcsineAdmission.amplitude,
        XiShiftedArcsineAdmission.monicScale]
  | succ n => exact amplitude_natDegree (by omega)

@[simp] theorem arc_amplitude_coeff_self (n : ℕ) :
    (Arc.amplitude n).coeff n = 1 := by
  have h := (arc_amplitude_monic_all n).coeff_natDegree
  rwa [arc_amplitude_natDegree_all] at h

theorem arc_amplitude_coeff_succ_eq_zero (n : ℕ) :
    (Arc.amplitude n).coeff (n + 1) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [arc_amplitude_natDegree_all]
  omega

theorem normalizedCentralBinom_jacobi_constants_of_recurrence
    {n : ℕ} (hn : 0 < n) {c : ℝ}
    (hrec : X * Arc.amplitude n =
      Arc.amplitude (n + 1) + (1 / 2 : ℝ) • Arc.amplitude n +
        c • Arc.amplitude (n - 1)) :
    HTGeometry.monicOrthoAlpha
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n = 1 / 2 ∧
      HTGeometry.monicOrthoBeta
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n = c := by
  have hj := HTGeometry.X_mul_monicOrtho
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm n
  rw [monicOrtho_normalizedCentralBinom_eq_arc_amplitude,
    monicOrtho_normalizedCentralBinom_eq_arc_amplitude,
    monicOrtho_normalizedCentralBinom_eq_arc_amplitude] at hj
  have hjTop := congrArg (fun p : Polynomial ℝ => p.coeff n) hj
  have hrTop := congrArg (fun p : Polynomial ℝ => p.coeff n) hrec
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul,
    arc_amplitude_coeff_self, smul_eq_mul] at hjTop hrTop
  have hprevZero : (Arc.amplitude (n - 1)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [arc_amplitude_natDegree_all]
    omega
  rw [hprevZero, mul_zero] at hjTop hrTop
  have halpha : HTGeometry.monicOrthoAlpha
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom n = 1 / 2 := by
    linarith
  have hjPrev := congrArg (fun p : Polynomial ℝ => p.coeff (n - 1)) hj
  have hrPrev := congrArg (fun p : Polynomial ℝ => p.coeff (n - 1)) hrec
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul,
    arc_amplitude_coeff_self, halpha, smul_eq_mul] at hjPrev hrPrev
  have hbeta : HTGeometry.monicOrthoBeta
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom n = c := by
    linarith
  exact ⟨halpha, hbeta⟩

theorem monicOrthoAlpha_normalizedCentralBinom (n : ℕ) :
    HTGeometry.monicOrthoAlpha
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n = 1 / 2 := by
  rcases n with _ | _ | n
  · exact monicOrthoAlpha_normalizedCentralBinom_zero
  · exact (normalizedCentralBinom_jacobi_constants_of_recurrence (n := 1) (by omega)
      arc_amplitude_recurrence_one).1
  · exact (normalizedCentralBinom_jacobi_constants_of_recurrence
      (n := n + 2) (by omega) (arc_amplitude_recurrence_of_two_le (by omega))).1

theorem monicOrthoBeta_normalizedCentralBinom_one :
    HTGeometry.monicOrthoBeta
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom 1 = 1 / 8 :=
  (normalizedCentralBinom_jacobi_constants_of_recurrence (n := 1) (by omega)
    arc_amplitude_recurrence_one).2

theorem monicOrthoBeta_normalizedCentralBinom_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    HTGeometry.monicOrthoBeta
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n = 1 / 16 :=
  (normalizedCentralBinom_jacobi_constants_of_recurrence (n := n) (by omega)
    (arc_amplitude_recurrence_of_two_le hn)).2

theorem dimensionlessAdmission_eq_monicOrtho
    {w : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    dimensionlessAdmission w n =
      HTGeometry.monicOrtho (xiShiftedFarRightNormalizedMoment w) n := by
  let s := xiShiftedFarRightNormalizedMoment w
  have hhead : (HTGeometry.momentHankelMatrix s n).PosDef := by
    let e : Fin n → Fin (n + 2) := fun i => ⟨i, by omega⟩
    have he : Function.Injective e := by
      intro i j hij
      apply Fin.ext
      simpa [e] using congrArg Fin.val hij
    have hsub := hH.submatrix he
    have heq : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (n + 2)).submatrix e e =
      HTGeometry.momentHankelMatrix s n := by
      ext i j
      rfl
    rwa [heq] at hsub
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hhead
  symm
  change HTGeometry.monicOrtho s n = HTGeometry.monicMomentAdmissionPolynomial s n
  apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    (ne_of_gt hhead.det_pos) (HTGeometry.monicOrtho_monic s n)
    (HTGeometry.natDegree_monicOrtho_eq s n)
  intro i
  rw [← HTGeometry.momentInner_def, HTGeometry.momentInner_comm]
  apply HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow le_rfl
  rw [Polynomial.degree_X_pow]
  exact_mod_cast i.isLt

theorem tendsto_dimensionless_monicOrthoFirstCoeff (n : ℕ) :
    Tendsto
      (fun w : ℝ => HTGeometry.monicOrthoFirstCoeff
        (xiShiftedFarRightNormalizedMoment w) n)
      atTop
      (nhds (HTGeometry.monicOrthoFirstCoeff
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n)) := by
  cases n with
  | zero => simp [HTGeometry.monicOrthoFirstCoeff]
  | succ n =>
      have hcoeff := tendsto_dimensionlessAdmission_coeff
        (n := n + 1) (by omega) n
      rw [← monicOrtho_normalizedCentralBinom_eq_arc_amplitude (n + 1)] at hcoeff
      apply hcoeff.congr'
      filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually
        (n + 3)] with w hH
      have hsmall : (HTGeometry.momentHankelMatrix
          (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef := by
        simpa [xiShiftedFarRightNormalizedHankelMatrix] using hH
      have heq := congrArg (fun p : Polynomial ℝ => p.coeff n)
        (dimensionlessAdmission_eq_monicOrtho hsmall)
      simpa [HTGeometry.monicOrthoFirstCoeff] using heq

theorem tendsto_dimensionless_monicOrthoSecondCoeff (n : ℕ) :
    Tendsto
      (fun w : ℝ => HTGeometry.monicOrthoSecondCoeff
        (xiShiftedFarRightNormalizedMoment w) n)
      atTop
      (nhds (HTGeometry.monicOrthoSecondCoeff
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n)) := by
  rcases n with _ | _ | n
  · simp [HTGeometry.monicOrthoSecondCoeff]
  · simp [HTGeometry.monicOrthoSecondCoeff]
  · have hcoeff := tendsto_dimensionlessAdmission_coeff
      (n := n + 2) (by omega) n
    rw [← monicOrtho_normalizedCentralBinom_eq_arc_amplitude (n + 2)] at hcoeff
    apply hcoeff.congr'
    filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually
      (n + 4)] with w hH
    have hsmall : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
      simpa [xiShiftedFarRightNormalizedHankelMatrix] using hH
    have heq := congrArg (fun p : Polynomial ℝ => p.coeff n)
      (dimensionlessAdmission_eq_monicOrtho hsmall)
    simpa [HTGeometry.monicOrthoSecondCoeff, Nat.add_assoc] using heq

theorem tendsto_dimensionless_monicOrthoAlpha (n : ℕ) :
    Tendsto
      (fun w : ℝ => HTGeometry.monicOrthoAlpha
        (xiShiftedFarRightNormalizedMoment w) n)
      atTop
      (nhds (1 / 2 : ℝ)) := by
  have hraw := (tendsto_dimensionless_monicOrthoFirstCoeff n).sub
    (tendsto_dimensionless_monicOrthoFirstCoeff (n + 1))
  have harc := HTGeometry.monicOrthoFirstCoeff_succ
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm n
  have hlim : HTGeometry.monicOrthoFirstCoeff
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n -
      HTGeometry.monicOrthoFirstCoeff
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom (n + 1) = 1 / 2 := by
    rw [harc, monicOrthoAlpha_normalizedCentralBinom]
    ring
  rw [hlim] at hraw
  apply hraw.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually
    (n + 2)] with w hH
  have hsmall : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hsmall
  rw [HTGeometry.monicOrthoFirstCoeff_succ_below hbelow (by omega)]
  ring

theorem tendsto_dimensionless_monicOrthoBeta
    {n : ℕ} (_hn : 0 < n) :
    Tendsto
      (fun w : ℝ => HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment w) n)
      atTop
      (nhds (HTGeometry.monicOrthoBeta
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n)) := by
  have hraw := (tendsto_dimensionless_monicOrthoSecondCoeff n).sub
      ((tendsto_dimensionless_monicOrthoAlpha n).mul
        (tendsto_dimensionless_monicOrthoFirstCoeff n)) |>.sub
      (tendsto_dimensionless_monicOrthoSecondCoeff (n + 1))
  have harc := HTGeometry.monicOrthoSecondCoeff_succ
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm n
  have hlim : HTGeometry.monicOrthoSecondCoeff
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom n -
        HTGeometry.monicOrthoAlpha
            GaloisForLFunctions.HTGeometry.normalizedCentralBinom n *
          HTGeometry.monicOrthoFirstCoeff
            GaloisForLFunctions.HTGeometry.normalizedCentralBinom n -
      HTGeometry.monicOrthoSecondCoeff
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom (n + 1) =
      HTGeometry.monicOrthoBeta
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n := by
    rw [harc]
    ring
  rw [monicOrthoAlpha_normalizedCentralBinom] at hlim
  rw [hlim] at hraw
  apply hraw.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually
    (n + 2)] with w hH
  have hsmall : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hsmall
  rw [HTGeometry.monicOrthoSecondCoeff_succ_below hbelow (by omega)]
  ring

theorem momentHankel_posDef_of_le
    {s : ℕ → ℝ} {m N : ℕ} (hmN : m ≤ N)
    (hH : (HTGeometry.momentHankelMatrix s N).PosDef) :
    (HTGeometry.momentHankelMatrix s m).PosDef := by
  let e : Fin m → Fin N := fun i => ⟨i, lt_of_lt_of_le i.isLt hmN⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg Fin.val hij
  have hsub := hH.submatrix he
  have heq : (HTGeometry.momentHankelMatrix s N).submatrix e e =
      HTGeometry.momentHankelMatrix s m := by
    ext i j
    rfl
  rwa [heq] at hsub

theorem sourceCoordinateAdmission_coeff_prev_prev
    {w : ℝ} (hw : w ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (sourceCoordinateAdmission w n).coeff (n - 2) =
      (w ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) * (dimensionlessAdmission w n).coeff (n - 2) := by
  simp only [sourceCoordinateAdmission, Polynomial.coeff_smul,
    Polynomial.comp_C_mul_X_coeff]
  have hsub : 2 * n = 2 * (n - 2) + 4 := by omega
  have hpow : (w ^ (2 : ℕ)) ^ (n - 2) = w ^ (2 * (n - 2)) := by
    rw [← pow_mul]
  rw [hpow, hsub, pow_add]
  have hz : w ^ (2 * (n - 2)) ≠ 0 := pow_ne_zero _ hw
  simp only [smul_eq_mul, inv_pow]
  field_simp [hw, hz]

theorem normalizedFirstCoeff_eq_square_mul_actualFirstCoeff
    {w : ℝ} (hw : 1 < w) (n : ℕ)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef) :
    HTGeometry.monicOrthoFirstCoeff (xiShiftedFarRightNormalizedMoment w) n =
      w ^ (2 : ℕ) * HTGeometry.monicOrthoFirstCoeff
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
  cases n with
  | zero => simp [HTGeometry.monicOrthoFirstCoeff]
  | succ n =>
      have hn : 0 < n + 1 := by omega
      have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
      have hNdet : (HTGeometry.momentHankelMatrix
          (xiShiftedFarRightNormalizedMoment w) (n + 1)).det ≠ 0 :=
        ne_of_gt (momentHankel_posDef_of_le
          (m := n + 1) (N := n + 3) (by omega) hN).det_pos
      have hAdet : (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 1)).det ≠ 0 :=
        ne_of_gt (momentHankel_posDef_of_le
          (m := n + 1) (N := n + 3) (by omega) hA).det_pos
      have hsource := sourceCoordinateAdmission_eq_actualAdmission
        hw hn hNdet hAdet
      have hNeq := dimensionlessAdmission_eq_monicOrtho hN
      have hAeq := xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hA
      have hcoeff : (sourceCoordinateAdmission w (n + 1)).coeff n =
          (w ^ (2 : ℕ))⁻¹ * (dimensionlessAdmission w (n + 1)).coeff n := by
        simpa using sourceCoordinateAdmission_coeff_prev
          (n := n + 1) hw0 hn
      change (HTGeometry.monicOrtho
          (xiShiftedFarRightNormalizedMoment w) (n + 1)).coeff n =
        w ^ (2 : ℕ) * (HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 1)).coeff n
      rw [← hNeq, ← hAeq, ← hsource, hcoeff]
      field_simp [hw0]

theorem normalizedSecondCoeff_eq_fourth_mul_actualSecondCoeff
    {w : ℝ} (hw : 1 < w) (n : ℕ)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef) :
    HTGeometry.monicOrthoSecondCoeff (xiShiftedFarRightNormalizedMoment w) n =
      w ^ (4 : ℕ) * HTGeometry.monicOrthoSecondCoeff
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
  rcases n with _ | _ | n
  · simp [HTGeometry.monicOrthoSecondCoeff]
  · simp [HTGeometry.monicOrthoSecondCoeff]
  · have hn : 2 ≤ n + 2 := by omega
    have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
    have hNdet : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (n + 2)).det ≠ 0 :=
      ne_of_gt (momentHankel_posDef_of_le
        (m := n + 2) (N := n + 4) (by omega) hN).det_pos
    have hAdet : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).det ≠ 0 :=
      ne_of_gt (momentHankel_posDef_of_le
        (m := n + 2) (N := n + 4) (by omega) hA).det_pos
    have hsource := sourceCoordinateAdmission_eq_actualAdmission
      hw (by omega) hNdet hAdet
    have hNeq := dimensionlessAdmission_eq_monicOrtho hN
    have hAeq := xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hA
    have hcoeff : (sourceCoordinateAdmission w (n + 2)).coeff n =
        (w ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) * (dimensionlessAdmission w (n + 2)).coeff n := by
      simpa using sourceCoordinateAdmission_coeff_prev_prev
        (n := n + 2) hw0 hn
    change (HTGeometry.monicOrtho
        (xiShiftedFarRightNormalizedMoment w) (n + 2)).coeff n =
      w ^ (4 : ℕ) * (HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).coeff n
    rw [← hNeq, ← hAeq, ← hsource, hcoeff]
    field_simp [hw0]

/-- Under reciprocal-mass dilation, diagonal Jacobi data have coordinate weight two. -/
theorem normalizedAlpha_eq_square_mul_actualAlpha
    {w : ℝ} (hw : 1 < w) (n : ℕ)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 3)).PosDef) :
    HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) n =
      w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
  have hNsmall : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hAsmall : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hfirstN := normalizedFirstCoeff_eq_square_mul_actualFirstCoeff
    hw n hNsmall hAsmall
  have hfirstN1 := normalizedFirstCoeff_eq_square_mul_actualFirstCoeff
    hw (n + 1) hN hA
  let hNbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hN
  let hAbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hA
  rw [HTGeometry.monicOrthoFirstCoeff_succ_below hNbelow (by omega)] at hfirstN1
  rw [HTGeometry.monicOrthoFirstCoeff_succ_below hAbelow (by omega)] at hfirstN1
  rw [hfirstN] at hfirstN1
  linarith

/-- Under reciprocal-mass dilation, lower Jacobi data have coordinate weight four. -/
theorem normalizedBeta_eq_fourth_mul_actualBeta
    {w : ℝ} (hw : 1 < w) (n : ℕ)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 3)).PosDef) :
    HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) n =
      w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
  have hNsmall : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hAsmall : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hsecondN := normalizedSecondCoeff_eq_fourth_mul_actualSecondCoeff
    hw n hNsmall hAsmall
  have hsecondN1 := normalizedSecondCoeff_eq_fourth_mul_actualSecondCoeff
    hw (n + 1) hN hA
  have halpha := normalizedAlpha_eq_square_mul_actualAlpha hw n hN hA
  have hfirst := normalizedFirstCoeff_eq_square_mul_actualFirstCoeff
    hw n hNsmall hAsmall
  let hNbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hN
  let hAbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hA
  rw [HTGeometry.monicOrthoSecondCoeff_succ_below hNbelow (by omega)] at hsecondN1
  rw [HTGeometry.monicOrthoSecondCoeff_succ_below hAbelow (by omega)] at hsecondN1
  rw [hsecondN, halpha, hfirst] at hsecondN1
  nlinarith [sq_nonneg (w ^ (2 : ℕ))]

/-- Dimensionless cumulative Jacobi trace selected by the adaptive source. -/
def dimensionlessCumulativeJacobiFlux (w : ℝ) (n : ℕ) : ℝ :=
  2 * (∑ j ∈ Finset.range n,
    HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j) +
    HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) n

/-- Dimensionless terminal curvature of the adaptive mixed amplitude/completed aggregate. -/
def dimensionlessTerminalJacobiRiccatiDefect (w : ℝ) (n : ℕ) : ℝ :=
  let s := xiShiftedFarRightNormalizedMoment w
  2 * (n : ℝ) * HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) +
    HTGeometry.monicOrthoAlpha s n * dimensionlessCumulativeJacobiFlux w n -
    (2 * ((n : ℝ) - 1) * HTGeometry.monicOrthoBeta s n -
      2 * ((n : ℝ) + 1) * HTGeometry.monicOrthoBeta s (n + 1) -
      HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ))

theorem normalizedAlpha_sum_eq_square_mul_actualAlpha_sum
    {w : ℝ} (hw : 1 < w) (n : ℕ)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 4)).PosDef) :
    (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j) =
      w ^ (2 : ℕ) * (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hNj : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (j + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hAj : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (j + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  exact normalizedAlpha_eq_square_mul_actualAlpha hw j hNj hAj

/-- Exact coordinate law: terminal curvature has reciprocal-mass weight four. -/
theorem dimensionlessTerminalJacobiRiccatiDefect_eq_fourth_mul_actual
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 4)).PosDef) :
    dimensionlessTerminalJacobiRiccatiDefect w n =
      w ^ (4 : ℕ) * xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect (w ^ (2 : ℕ)) n := by
  have hNn : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hAn : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hNn1 : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 1 + 3)).PosDef := by
    simpa [Nat.add_assoc] using hN
  have hAn1 : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 1 + 3)).PosDef := by
    simpa [Nat.add_assoc] using hA
  have halpha := normalizedAlpha_eq_square_mul_actualAlpha hw n hNn hAn
  have hbeta := normalizedBeta_eq_fourth_mul_actualBeta hw n hNn hAn
  have hbeta1 := normalizedBeta_eq_fourth_mul_actualBeta hw (n + 1) hNn1 hAn1
  have hsum := normalizedAlpha_sum_eq_square_mul_actualAlpha_sum hw n hN hA
  have hAtrace : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  rw [dimensionlessTerminalJacobiRiccatiDefect,
    dimensionlessCumulativeJacobiFlux,
    xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect,
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hAtrace,
    halpha, hbeta, hbeta1, hsum]
  ring

/-- The dimensionless cumulative source trace has its exact arcsine boundary value. -/
theorem tendsto_dimensionlessCumulativeJacobiFlux (n : ℕ) :
    Tendsto (fun w : ℝ => dimensionlessCumulativeJacobiFlux w n)
      atTop (nhds (((2 * n + 1 : ℕ) : ℝ) / 2)) := by
  have hsum := tendsto_finsetSum (Finset.range n)
    (fun j _hj => tendsto_dimensionless_monicOrthoAlpha j)
  have h := (hsum.const_mul 2).add (tendsto_dimensionless_monicOrthoAlpha n)
  convert h using 1
  · simp [dimensionlessCumulativeJacobiFlux]
  · simp
    ring_nf

theorem tendsto_dimensionlessWeightedBeta
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ => ((n : ℝ) - 1) *
        HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) n)
      atTop (nhds (((n : ℝ) - 1) / 16)) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · simp
  · have h := (tendsto_dimensionless_monicOrthoBeta
    (n := n + 2) (by omega)).const_mul (((n + 2 : ℕ) : ℝ) - 1)
    rw [monicOrthoBeta_normalizedCentralBinom_of_two_le (by omega)] at h
    have hconst : (((n + 2 : ℕ) : ℝ) - 1) * (1 / 16) =
        (((n + 2 : ℕ) : ℝ) - 1) / 16 := by ring
    rwa [hconst] at h

/-- Fixed-degree terminal source curvature converges to the forced arcsine constant. -/
theorem tendsto_dimensionlessTerminalJacobiRiccatiDefect
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ => dimensionlessTerminalJacobiRiccatiDefect w n)
      atTop (nhds (((4 * n + 3 : ℕ) : ℝ) / 4)) := by
  have ha := tendsto_dimensionless_monicOrthoAlpha n
  have hflux := tendsto_dimensionlessCumulativeJacobiFlux n
  have hweighted := tendsto_dimensionlessWeightedBeta hn
  have hbeta1 := tendsto_dimensionless_monicOrthoBeta (n := n + 1) (by omega)
  rw [monicOrthoBeta_normalizedCentralBinom_of_two_le (by omega)] at hbeta1
  have h := ((ha.pow 2).const_mul (2 * (n : ℝ))).add (ha.mul hflux) |>.sub
    ((hweighted.const_mul 2).sub
      (hbeta1.const_mul (2 * ((n : ℝ) + 1))) |>.sub (ha.pow 2))
  convert h using 1
  · simp [dimensionlessTerminalJacobiRiccatiDefect]
    funext w
    ring
  · simp
    ring

/-- Actual completed curvature has a positive fixed-degree far-right boundary after its forced
weight-four renormalization. -/
theorem tendsto_fourth_mul_xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_squareParam
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ => w ^ (4 : ℕ) *
        xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect (w ^ (2 : ℕ)) n)
      atTop (nhds (((4 * n + 3 : ℕ) : ℝ) / 4)) := by
  apply (tendsto_dimensionlessTerminalJacobiRiccatiDefect hn).congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 4),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 4),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hA' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 4)).PosDef := by
    have heq : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 4) =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 4) := by
      rfl
    rwa [← heq]
  exact (dimensionlessTerminalJacobiRiccatiDefect_eq_fourth_mul_actual
    hw hn hN' hA')

/-- Degree normalization exposes universal boundary curvature `1/4`. -/
theorem tendsto_degreeNormalized_xiShiftedCanonicalAdmissionTerminalCurvature
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ =>
        (w ^ (4 : ℕ) * xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect (w ^ (2 : ℕ)) n) /
          ((4 * n + 3 : ℕ) : ℝ))
      atTop (nhds (1 / 4 : ℝ)) := by
  have h :=
    (tendsto_fourth_mul_xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_squareParam
      hn).div_const (((4 * n + 3 : ℕ) : ℝ))
  convert h using 1
  push_cast
  field_simp

/-- Every fixed positive-degree actual terminal curvature is eventually strictly positive. -/
theorem xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_squareParam_eventually_pos
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect (w ^ (2 : ℕ)) n := by
  have hlim :=
    tendsto_fourth_mul_xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_squareParam hn
  have hconst : 0 < (((4 * n + 3 : ℕ) : ℝ) / 4) := by positivity
  have hnhds : Set.Ioi (0 : ℝ) ∈ nhds (((4 * n + 3 : ℕ) : ℝ) / 4) :=
    isOpen_Ioi.mem_nhds hconst
  have hscaled := hlim.eventually hnhds
  filter_upwards [hscaled, eventually_gt_atTop (1 : ℝ)] with w hpos hw
  exact pos_of_mul_pos_right hpos (pow_nonneg (le_of_lt (lt_trans zero_lt_one hw)) 4)

/-- Consequently, the actual canonical odd current has strictly negative terminal drift at every
fixed positive degree. -/
theorem deriv_xiShiftedCanonicalAdmissionOddCurrent_squareParam_eventually_neg
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ w : ℝ in atTop,
      deriv (fun y => xiShiftedCanonicalAdmissionOddCurrent y n) (w ^ (2 : ℕ)) < 0 := by
  filter_upwards [
    xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_squareParam_eventually_pos hn,
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2),
    eventually_gt_atTop (1 : ℝ)] with w hdef hH hw
  have hH' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef := by
    have heq : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 2) =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2) := by
      rfl
    rwa [← heq]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH'
  have hnorm : 0 < HTGeometry.monicOrthoNormSq
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hderiv :=
    hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_neg_norm_mul_terminalRiccatiDefect
      (sq_pos_of_pos (lt_trans zero_lt_one hw)) hn hH'
  have hderiv' : HasDerivAt (fun y => xiShiftedCanonicalAdmissionOddCurrent y n)
      (-HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n *
        xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect (w ^ (2 : ℕ)) n) (w ^ (2 : ℕ)) := by
    simpa [xiShiftedCanonicalAdmissionOddCurrent] using hderiv
  rw [hderiv'.deriv]
  nlinarith [mul_pos hnorm hdef]

/-- In actual mass coordinates the forced curvature normalization is `y²`. -/
theorem tendsto_square_mul_xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun y : ℝ => y ^ (2 : ℕ) * xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect y n)
      atTop (nhds (((4 * n + 3 : ℕ) : ℝ) / 4)) := by
  have h :=
    (tendsto_fourth_mul_xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_squareParam
      hn).comp Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply]
  rw [show Real.sqrt y ^ (4 : ℕ) = (Real.sqrt y ^ (2 : ℕ)) ^ (2 : ℕ) by ring,
    Real.sq_sqrt hy]

/-- Actual terminal curvature is positive on a complete far-right mass chamber. -/
theorem xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_eventually_pos
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ y : ℝ in atTop,
      0 < xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect y n := by
  have hsqrt := Real.tendsto_sqrt_atTop.eventually
    (xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_squareParam_eventually_pos hn)
  filter_upwards [hsqrt, eventually_ge_atTop (0 : ℝ)] with y hpos hy
  rwa [Real.sq_sqrt hy] at hpos

/-- Actual canonical odd current decreases on a complete far-right mass chamber. -/
theorem deriv_xiShiftedCanonicalAdmissionOddCurrent_eventually_neg
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ y : ℝ in atTop,
      deriv (fun v => xiShiftedCanonicalAdmissionOddCurrent v n) y < 0 := by
  have hsqrt := Real.tendsto_sqrt_atTop.eventually
    (deriv_xiShiftedCanonicalAdmissionOddCurrent_squareParam_eventually_neg hn)
  filter_upwards [hsqrt, eventually_ge_atTop (0 : ℝ)] with y hneg hy
  rwa [Real.sq_sqrt hy] at hneg

end
end XiShiftedCanonicalAdmission
end RHTower
