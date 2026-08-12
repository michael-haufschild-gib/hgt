import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionEvenContactSource

/-!
# Quantitative curvature quotient at every shifted-Xi first contact

Immediate odd contact is not the only boundary branch: a flat Padé null flag can persist until a
later odd or even defect.  This module shows that the first surviving defect is never
quantitatively invisible.  Two source-selected lifted null descendants span a hyperbolic plane;
an adaptive bilinear completion converts their first nonzero coupling into exact negative Hankel
energy.  The actual integral Lipschitz law then charges that energy to one scalar terminal
frontier.

Thus a zero-contact plateau changes the degree at which curvature is charged, but cannot erase
the charge.  No fixed reporter, eigenvector choice, compactness, or post-aggregation orientation
enters.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Adaptive completion of a zero-energy polynomial by a source-selected transverse polynomial.
The completion denominator is always positive and requires no sign choice for transverse
self-energy. -/
def xiShiftedAdaptiveNullPairPolynomial
    (y : ℝ) (U V : Polynomial ℝ) : Polynomial ℝ :=
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := HTGeometry.momentInner s U V
  let a := HTGeometry.momentInner s V V
  U + (-γ / (|a| + 1)) • V

/-- The adaptive completion remains in every finite coordinate block containing both input
polynomials. -/
theorem natDegree_xiShiftedAdaptiveNullPairPolynomial_lt
    {y : ℝ} {N : ℕ} {U V : Polynomial ℝ}
    (hU : U.natDegree < N) (hV : V.natDegree < N) :
    (xiShiftedAdaptiveNullPairPolynomial y U V).natDegree < N := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := HTGeometry.momentInner s U V
  let a := HTGeometry.momentInner s V V
  unfold xiShiftedAdaptiveNullPairPolynomial
  dsimp only
  calc
    (U + (-γ / (|a| + 1)) • V).natDegree ≤
        max U.natDegree (((-γ / (|a| + 1)) • V).natDegree) :=
      Polynomial.natDegree_add_le _ _
    _ ≤ max U.natDegree V.natDegree :=
      max_le_max le_rfl (Polynomial.natDegree_smul_le _ _)
    _ < N := max_lt hU hV

/-- Finite coefficient realization preserves the exact shifted-Xi moment energy. -/
theorem xiShiftedMomentHankelQuadratic_toFn_eq_momentInner
    {y : ℝ} {N : ℕ} {A : Polynomial ℝ} (hA : A.natDegree < N) :
    xiShiftedMomentHankelQuadratic y N (Polynomial.toFn N A) =
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) A A := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let x : Fin N → ℝ := Polynomial.toFn N A
  have hx : Polynomial.ofFn N x = A :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hA
  have hinner := HTGeometry.momentInner_ofFn_ofFn s N x x
  rw [hx] at hinner
  change x ⬝ᵥ (HTGeometry.momentHankelMatrix s N).mulVec x =
    HTGeometry.momentInner s A A
  exact hinner.symm

/-- **Universal adaptive null-pair energy.**  A zero self-energy and nonzero mixed source
coupling produce exact negative completed energy. -/
theorem momentInner_xiShiftedAdaptiveNullPairPolynomial_self_eq
    {y : ℝ} (U V : Polynomial ℝ)
    (hUU : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) U U = 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let γ := HTGeometry.momentInner s U V
    let a := HTGeometry.momentInner s V V
    HTGeometry.momentInner s
        (xiShiftedAdaptiveNullPairPolynomial y U V)
        (xiShiftedAdaptiveNullPairPolynomial y U V) =
      -(γ ^ 2 * (2 * (|a| + 1) - a) / (|a| + 1) ^ 2) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := HTGeometry.momentInner s U V
  let a := HTGeometry.momentInner s V V
  have hD : |a| + 1 ≠ 0 := ne_of_gt (by positivity)
  dsimp only
  unfold xiShiftedAdaptiveNullPairPolynomial
  dsimp only
  simp only [HTGeometry.momentInner_add_left, HTGeometry.momentInner_add_right,
    HTGeometry.momentInner_smul_left, HTGeometry.momentInner_smul_right,
    hUU]
  rw [HTGeometry.momentInner_comm s V U]
  change 0 + (-γ / (|a| + 1)) * γ +
      (-γ / (|a| + 1)) *
        (γ + (-γ / (|a| + 1)) * a) = _
  field_simp
  ring

/-- The exact adaptive energy is strictly negative whenever first transverse source coupling is
nonzero. -/
theorem momentInner_xiShiftedAdaptiveNullPairPolynomial_self_neg
    {y : ℝ} (U V : Polynomial ℝ)
    (hUU : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) U U = 0)
    (hUV : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) U V ≠ 0) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (xiShiftedAdaptiveNullPairPolynomial y U V)
        (xiShiftedAdaptiveNullPairPolynomial y U V) < 0 := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := HTGeometry.momentInner s U V
  let a := HTGeometry.momentInner s V V
  rw [momentInner_xiShiftedAdaptiveNullPairPolynomial_self_eq U V hUU]
  have hγ : 0 < γ ^ 2 := sq_pos_of_ne_zero (by simpa only [γ, s] using hUV)
  have hfactor : 0 < 2 * (|a| + 1) - a := by
    linarith [le_abs_self a, abs_nonneg a]
  have hden : 0 < (|a| + 1) ^ 2 := sq_pos_of_pos (by positivity)
  exact neg_neg_of_pos (div_pos (mul_pos hγ hfactor) hden)

/-- **Sharp adaptive null-pair frontier law.**  Exact source energy divided by actual global
integral Lipschitz cost is a lower bound for terminal-frontier displacement. -/
theorem add_adaptiveNullPairEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
    {y : ℝ} (hy : 0 < y) {k : ℕ} (U V : Polynomial ℝ)
    (hU : U.natDegree < k + 2) (hV : V.natDegree < k + 2)
    (hUU : HTGeometry.momentInner
      (fun j => (xiShiftedReciprocalMoment y j).re) U U = 0)
    (hUV : HTGeometry.momentInner
      (fun j => (xiShiftedReciprocalMoment y j).re) U V ≠ 0) :
    let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
    let γ := HTGeometry.momentInner s U V
    let a := HTGeometry.momentInner s V V
    let A := xiShiftedAdaptiveNullPairPolynomial y U V
    let x := Polynomial.toFn (k + 2) A
    y + (γ ^ 2 * (2 * (|a| + 1) - a) / (|a| + 1) ^ 2) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
      xiShiftedHigherBlockTerminalFrontier k := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  let γ := HTGeometry.momentInner s U V
  let a := HTGeometry.momentInner s V V
  let A := xiShiftedAdaptiveNullPairPolynomial y U V
  let x := Polynomial.toFn (k + 2) A
  have hA : A.natDegree < k + 2 :=
    natDegree_xiShiftedAdaptiveNullPairPolynomial_lt hU hV
  have henergy : xiShiftedMomentHankelQuadratic y (k + 2) x =
      -(γ ^ 2 * (2 * (|a| + 1) - a) / (|a| + 1) ^ 2) := by
    rw [xiShiftedMomentHankelQuadratic_toFn_eq_momentInner hA]
    simpa only [s, γ, a, A] using
      momentInner_xiShiftedAdaptiveNullPairPolynomial_self_eq U V hUU
  have hneg : xiShiftedMomentHankelQuadratic y (k + 2) x < 0 := by
    rw [xiShiftedMomentHankelQuadratic_toFn_eq_momentInner hA]
    exact momentInner_xiShiftedAdaptiveNullPairPolynomial_self_neg U V hUU hUV
  have hfront :=
    add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier_sharp hy x hneg
  dsimp only at hfront ⊢
  rw [henergy] at hfront
  simpa only [neg_neg] using hfront

/-- **Quantitative odd first-contact renewal.**  A first Padé defect at order `2n+2m+1`
charges exact adaptive curvature to frontier `n+m`, even after an arbitrarily long zero-contact
plateau. -/
theorem add_firstOddPadeDefectAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c j = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * m + 1)) ≠ 0) :
    let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let U := P * X ^ m
    let V := P * X ^ (m + 1)
    let δ := xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1))
    let a := HTGeometry.momentInner s V V
    let A := xiShiftedAdaptiveNullPairPolynomial y U V
    let x := Polynomial.toFn (n + m + 2) A
    y + (δ ^ 2 * (2 * (|a| + 1) - a) / (|a| + 1) ^ 2) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
      xiShiftedHigherBlockTerminalFrontier (n + m) := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let U := P * X ^ m
  let V := P * X ^ (m + 1)
  let δ := xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1))
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hU : U.natDegree < n + m + 2 := by
    dsimp only [U]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hV : V.natDegree < n + m + 2 := by
    dsimp only [V]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow (m + 1)), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hUU : HTGeometry.momentInner s U U = 0 := by
    simpa only [s, U, P] using
      (momentInner_liftedNullPair_eq_zero_of_odd_contact
        c hlast hzero (i := m) (j := m) (by omega))
  have hUVeq : HTGeometry.momentInner s U V = δ := by
    simpa only [s, U, V, P, δ] using
      (momentInner_liftedNullPair_eq_first_odd_defect
        c hlast hzero (i := m) (j := m + 1) (by omega))
  have hUV : HTGeometry.momentInner s U V ≠ 0 := by
    rw [hUVeq]
    exact hfirst
  have hfront :=
    add_adaptiveNullPairEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
      hy U V hU hV hUU hUV
  dsimp only at hfront ⊢
  rw [hUVeq] at hfront
  exact hfront

/-- **Quantitative even first-contact renewal.**  A positive or negative first even defect
charges exact adaptive curvature to frontier `n+m`.  In particular, positive one-block rank fill
does not hide quantitative escape. -/
theorem add_firstEvenPadeDefectAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (hm : 0 < m)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ j < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect y c j = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) ≠ 0) :
    let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let U := P * X ^ (m - 1)
    let V := P * X ^ (m + 1)
    let δ := xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m)
    let a := HTGeometry.momentInner s V V
    let A := xiShiftedAdaptiveNullPairPolynomial y U V
    let x := Polynomial.toFn (n + m + 2) A
    y + (δ ^ 2 * (2 * (|a| + 1) - a) / (|a| + 1) ^ 2) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
      xiShiftedHigherBlockTerminalFrontier (n + m) := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let U := P * X ^ (m - 1)
  let V := P * X ^ (m + 1)
  let δ := xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m)
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hU : U.natDegree < n + m + 2 := by
    dsimp only [U]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow (m - 1)), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hV : V.natDegree < n + m + 2 := by
    dsimp only [V]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow (m + 1)), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hzeroOdd : ∀ j < 2 * n + (2 * (m - 1) + 1),
      xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
    intro j hj
    exact hzero j (by omega)
  have hUU : HTGeometry.momentInner s U U = 0 := by
    simpa only [s, U, P] using
      (momentInner_liftedNullPair_eq_zero_of_odd_contact
        c hlast hzeroOdd (i := m - 1) (j := m - 1) (by omega))
  have hpoly : U * V = (P * X ^ m) ^ 2 := by
    dsimp only [U, V]
    calc
      (P * X ^ (m - 1)) * (P * X ^ (m + 1)) =
          P ^ 2 * (X ^ (m - 1) * X ^ (m + 1)) := by ring
      _ = P ^ 2 * X ^ ((m - 1) + (m + 1)) := by
        congr 1
        exact (pow_add X (m - 1) (m + 1)).symm
      _ = P ^ 2 * X ^ (2 * m) := by
        rw [show (m - 1) + (m + 1) = 2 * m by omega]
      _ = P ^ 2 * (X ^ m * X ^ m) := by
        rw [show 2 * m = m + m by omega, pow_add]
      _ = (P * X ^ m) ^ 2 := by ring
  have hUVeq : HTGeometry.momentInner s U V = δ := by
    have heven := xiShiftedHankelBoundaryPadeDefect_first_even_eq_liftedSquare
      c hlast hm hzero
    rw [HTGeometry.momentInner_def, hpoly]
    exact heven.symm
  have hUV : HTGeometry.momentInner s U V ≠ 0 := by
    rw [hUVeq]
    exact hfirst
  have hfront :=
    add_adaptiveNullPairEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
      hy U V hU hV hUU hUV
  dsimp only at hfront ⊢
  rw [hUVeq] at hfront
  exact hfront

/-- **Parity-complete first-contact frontier certificate.**  Every positive shifted-Xi flat face
with positive head has, at some finite weakly higher degree, a source-selected negative witness
whose normalized negative energy gives a strictly positive quantitative terminal-frontier price.
This packages odd and even first contacts without assuming immediate monic remainder is nonzero. -/
theorem exists_sourceAdaptive_frontierCertificate_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    ∃ k : ℕ, n ≤ k ∧ ∃ x : Fin (k + 2) → ℝ,
      0 < -xiShiftedMomentHankelQuadratic y (k + 2) x ∧
      y + (-xiShiftedMomentHankelQuadratic y (k + 2) x) /
          xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
        xiShiftedHigherBlockTerminalFrontier k := by
  have hcertificate (k : ℕ) (U V : Polynomial ℝ)
      (hU : U.natDegree < k + 2) (hV : V.natDegree < k + 2)
      (hUU : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U U = 0)
      (hUV : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U V ≠ 0) :
      ∃ x : Fin (k + 2) → ℝ,
        0 < -xiShiftedMomentHankelQuadratic y (k + 2) x ∧
        y + (-xiShiftedMomentHankelQuadratic y (k + 2) x) /
            xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
          xiShiftedHigherBlockTerminalFrontier k := by
    let A := xiShiftedAdaptiveNullPairPolynomial y U V
    let x := Polynomial.toFn (k + 2) A
    have hA : A.natDegree < k + 2 :=
      natDegree_xiShiftedAdaptiveNullPairPolynomial_lt hU hV
    have hneg : xiShiftedMomentHankelQuadratic y (k + 2) x < 0 := by
      rw [xiShiftedMomentHankelQuadratic_toFn_eq_momentInner hA]
      exact momentInner_xiShiftedAdaptiveNullPairPolynomial_self_neg U V hUU hUV
    exact ⟨x, neg_pos.mpr hneg,
      add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier_sharp hy x hneg⟩
  obtain ⟨d, hd, hzero, hfirst⟩ :=
    exists_first_xiShiftedHankelBoundaryPadeDefect hy c hhead hc hlast
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hdform : d = 2 * m := by omega
    have hmpos : 0 < m := by omega
    let U := P * X ^ (m - 1)
    let V := P * X ^ (m + 1)
    have hU : U.natDegree < n + m + 2 := by
      dsimp only [U]
      rw [hP.natDegree_mul (Polynomial.monic_X_pow (m - 1)), hPdeg,
        Polynomial.natDegree_X_pow]
      omega
    have hV : V.natDegree < n + m + 2 := by
      dsimp only [V]
      rw [hP.natDegree_mul (Polynomial.monic_X_pow (m + 1)), hPdeg,
        Polynomial.natDegree_X_pow]
      omega
    have hzeroEven : ∀ j < 2 * n + 2 * m,
        xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
      intro j hj
      exact hzero j (by omega)
    have hzeroOdd : ∀ j < 2 * n + (2 * (m - 1) + 1),
        xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
      intro j hj
      exact hzero j (by omega)
    have hUU : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U U = 0 := by
      simpa only [U, P] using
        (momentInner_liftedNullPair_eq_zero_of_odd_contact
          c hlast hzeroOdd (i := m - 1) (j := m - 1) (by omega))
    have hpoly : U * V = (P * X ^ m) ^ 2 := by
      dsimp only [U, V]
      calc
        (P * X ^ (m - 1)) * (P * X ^ (m + 1)) =
            P ^ 2 * (X ^ (m - 1) * X ^ (m + 1)) := by ring
        _ = P ^ 2 * X ^ ((m - 1) + (m + 1)) := by
          congr 1
          exact (pow_add X (m - 1) (m + 1)).symm
        _ = P ^ 2 * X ^ (2 * m) := by
          rw [show (m - 1) + (m + 1) = 2 * m by omega]
        _ = P ^ 2 * (X ^ m * X ^ m) := by
          rw [show 2 * m = m + m by omega, pow_add]
        _ = (P * X ^ m) ^ 2 := by ring
    have hUVeq : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U V =
        xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) := by
      have heven := xiShiftedHankelBoundaryPadeDefect_first_even_eq_liftedSquare
        c hlast hmpos hzeroEven
      rw [HTGeometry.momentInner_def, hpoly]
      exact heven.symm
    have hUV : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U V ≠ 0 := by
      rw [hUVeq]
      simpa only [hdform] using hfirst
    exact ⟨n + m, by omega, hcertificate (n + m) U V hU hV hUU hUV⟩
  · have hdform : d = 2 * m + 1 := by omega
    let U := P * X ^ m
    let V := P * X ^ (m + 1)
    have hU : U.natDegree < n + m + 2 := by
      dsimp only [U]
      rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
        Polynomial.natDegree_X_pow]
      omega
    have hV : V.natDegree < n + m + 2 := by
      dsimp only [V]
      rw [hP.natDegree_mul (Polynomial.monic_X_pow (m + 1)), hPdeg,
        Polynomial.natDegree_X_pow]
      omega
    have hzeroOdd : ∀ j < 2 * n + (2 * m + 1),
        xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
      intro j hj
      exact hzero j (by omega)
    have hUU : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U U = 0 := by
      simpa only [U, P] using
        (momentInner_liftedNullPair_eq_zero_of_odd_contact
          c hlast hzeroOdd (i := m) (j := m) (by omega))
    have hUVeq : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U V =
        xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) := by
      simpa only [U, V, P] using
        (momentInner_liftedNullPair_eq_first_odd_defect
          c hlast hzeroOdd (i := m) (j := m + 1) (by omega))
    have hUV : HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) U V ≠ 0 := by
      rw [hUVeq]
      simpa only [hdform] using hfirst
    exact ⟨n + m, by omega, hcertificate (n + m) U V hU hV hUU hUV⟩

end

end RHTower
