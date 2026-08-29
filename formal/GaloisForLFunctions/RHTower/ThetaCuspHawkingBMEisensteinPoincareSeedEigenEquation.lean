import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinModularGeneratorInvariance

/-!
# Actual hyperbolic eigen-equation for every primitive Poincaré seed

Corpus-derived conjecture C-A.9q closes the analytic seed calculation needed by
the honest modular Green/Stokes route.  For every primitive integer pair, this
module constructs the genuine horizontal and vertical first and second real
derivatives of `(y / |c z + d|²)^s` and proves

`y² (∂ₓ² + ∂ᵧ²) seed = s (s - 1) seed`.

The centered specialization `s = 1/2 + u` is exactly the corpus geometric
eigenvalue `u² - 1/4`.  Intended RH chain:

seed eigen-equation → termwise Poincaré eigenfunction → modular Green/Stokes →
polarized BM `++−` source → conserved left-QNM projection → HC94 clock defect → RH.

All results are unconditional.  The jet expressions below are certified as
actual derivatives rather than introduced as formal differential proxies.
-/

open Complex Real

namespace RHTower
noncomputable section

lemma d4BM_hasDerivAt_ofReal_cpow
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ w)
      (w * (r : ℂ) ^ (w - 1)) r := by
  have hslit : (r : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using hr
  have h := (hasDerivAt_id (r : ℂ)).cpow_const (c := w) hslit
  simpa using h.comp_ofReal

def d4BMPoincareHorizontalLinear
    (z : D4BMUpperHalfPlaneCoordinate) (p : D4BMPrimitiveIntegerPair) : ℝ :=
  (p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)

def d4BMPoincareSeedHorizontalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (-2 * s * (p.pair.1 : ℂ) * (d4BMPoincareHorizontalLinear z p : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ)) * d4BMPoincareSeed z s p

def d4BMPoincareSeedHorizontalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (-2 * s * (p.pair.1 : ℂ) ^ 2 /
        (d4BMPoincareQuadratic z p.pair : ℂ) +
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
        (d4BMPoincareHorizontalLinear z p : ℂ) ^ 2 /
          (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2) *
    d4BMPoincareSeed z s p

def d4BMPoincareSeedVerticalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (s / (z.y : ℂ) -
      2 * s * (p.pair.1 : ℂ) ^ 2 * (z.y : ℂ) /
        (d4BMPoincareQuadratic z p.pair : ℂ)) * d4BMPoincareSeed z s p

def d4BMPoincareSeedVerticalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (s * (s - 1) / (z.y : ℂ) ^ 2 -
      2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
        (d4BMPoincareQuadratic z p.pair : ℂ) +
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) ^ 2 /
        (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2) *
    d4BMPoincareSeed z s p

def d4BMPoincareSeedVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) : ℂ :=
  ((y / (((p.pair.1 : ℝ) * y) ^ 2 +
      ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2) : ℝ) : ℂ) ^ s

def d4BMPoincareSeedVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) : ℂ :=
  (s / (y : ℂ) -
      2 * s * (p.pair.1 : ℂ) ^ 2 * (y : ℂ) /
        ((((p.pair.1 : ℝ) * y) ^ 2 +
          ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ)) *
    d4BMPoincareSeedVerticalSlice z s p y

theorem d4BM_poincareSeedVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedVerticalSlice z s p z.y = d4BMPoincareSeed z s p := by
  rfl

theorem d4BM_poincareSeedVerticalFirstJetSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedVerticalFirstJetSlice z s p z.y =
      d4BMPoincareSeedVerticalFirstJet z s p := by
  rfl

theorem hasDerivAt_d4BMPoincareSeed_vertical
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt (d4BMPoincareSeedVerticalSlice z s p)
      (d4BMPoincareSeedVerticalFirstJet z s p) z.y := by
  let c : ℝ := p.pair.1
  let u : ℝ := c * z.x + p.pair.2
  let Q : ℝ → ℝ := fun y => (c * y) ^ 2 + u ^ 2
  let r : ℝ → ℝ := fun y => y / Q y
  have hQpos : 0 < Q z.y := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQneR : Q z.y ≠ 0 := hQpos.ne'
  have hrpos : 0 < r z.y := div_pos z.y_pos hQpos
  have hQderiv : HasDerivAt Q (2 * c ^ 2 * z.y) z.y := by
    dsimp only [Q]
    have hcy : HasDerivAt (fun y : ℝ => c * y) c z.y := by
      simpa using (hasDerivAt_id z.y).const_mul c
    exact ((hcy.pow 2).add (hasDerivAt_const z.y (u ^ 2))).congr_deriv (by ring)
  have hrderiv : HasDerivAt r
      ((Q z.y - z.y * (2 * c ^ 2 * z.y)) / (Q z.y) ^ 2) z.y := by
    dsimp only [r]
    exact ((hasDerivAt_id z.y).div hQderiv hQneR).congr_deriv (by
      simp only [id_eq]
      ring)
  have hpow := (d4BM_hasDerivAt_ofReal_cpow s hrpos).scomp z.y hrderiv
  have hfun : d4BMPoincareSeedVerticalSlice z s p =
      (fun t : ℝ => (t : ℂ) ^ s) ∘ r := by
    funext y
    rfl
  rw [hfun]
  apply hpow.congr_deriv
  let RC : ℂ := (r z.y : ℂ)
  let QC : ℂ := (Q z.y : ℂ)
  have hRCne : RC ≠ 0 := by
    dsimp only [RC]
    exact_mod_cast hrpos.ne'
  have hQCne : QC ≠ 0 := by
    dsimp only [QC]
    exact_mod_cast hQneR
  have hRC : RC = (z.y : ℂ) / QC := by
    dsimp only [RC, QC, r]
    push_cast
    rfl
  have hcpow : RC ^ (s - 1) * RC = RC ^ s := by
    calc
      RC ^ (s - 1) * RC = RC ^ (s - 1) * RC ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = RC ^ ((s - 1) + 1) := (Complex.cpow_add _ _ hRCne).symm
      _ = RC ^ s := by ring_nf
  have hscalar :
      (((Q z.y - z.y * (2 * c ^ 2 * z.y)) / (Q z.y) ^ 2 : ℝ) : ℂ) =
        (QC - (z.y : ℂ) * (2 * (c : ℂ) ^ 2 * (z.y : ℂ))) / QC ^ 2 := by
    dsimp only [QC]
    push_cast
    ring
  rw [Complex.real_smul, hscalar]
  calc
    ((QC - (z.y : ℂ) * (2 * (c : ℂ) ^ 2 * (z.y : ℂ))) / QC ^ 2) *
          (s * RC ^ (s - 1)) =
        (s / (z.y : ℂ) -
          2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / QC) *
          (RC ^ (s - 1) * RC) := by
            rw [hRC]
            have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
            field_simp [hQCne, hy]
    _ = (s / (z.y : ℂ) -
          2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / QC) * RC ^ s := by
      rw [hcpow]
    _ = d4BMPoincareSeedVerticalFirstJet z s p := by
      unfold d4BMPoincareSeedVerticalFirstJet d4BMPoincareSeed d4BMPoincareQuadratic
      dsimp only [c, u, QC, Q, RC, r]
      push_cast
      rfl

theorem hasDerivAt_d4BMPoincareSeedVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt (d4BMPoincareSeedVerticalFirstJetSlice z s p)
      (d4BMPoincareSeedVerticalSecondJet z s p) z.y := by
  let c : ℝ := p.pair.1
  let u : ℝ := c * z.x + p.pair.2
  let Q : ℝ → ℝ := fun y => (c * y) ^ 2 + u ^ 2
  let B : ℝ → ℂ := fun y =>
    s / (y : ℂ) - 2 * s * (c : ℂ) ^ 2 * (y : ℂ) / (Q y : ℂ)
  let f : ℝ → ℂ := d4BMPoincareSeedVerticalSlice z s p
  have hQpos : 0 < Q z.y := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQneR : Q z.y ≠ 0 := hQpos.ne'
  have hQne : (Q z.y : ℂ) ≠ 0 := by exact_mod_cast hQneR
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hidR : HasDerivAt (fun y : ℝ => y) 1 z.y := hasDerivAt_id z.y
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 z.y := hidR.ofReal_comp
  have hQderivR : HasDerivAt Q (2 * c ^ 2 * z.y) z.y := by
    dsimp only [Q]
    have hcy : HasDerivAt (fun y : ℝ => c * y) c z.y := by
      simpa using (hasDerivAt_id z.y).const_mul c
    exact ((hcy.pow 2).add (hasDerivAt_const z.y (u ^ 2))).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun y : ℝ => (Q y : ℂ))
      ((2 * c ^ 2 * z.y : ℝ) : ℂ) z.y := hQderivR.ofReal_comp
  have hBraw :=
    ((hasDerivAt_const z.y s).div hid hy).sub
      ((hid.const_mul (2 * s * (c : ℂ) ^ 2)).div hQderiv hQne)
  have hBderiv : HasDerivAt B
      (-s / (z.y : ℂ) ^ 2 -
        2 * s * (c : ℂ) ^ 2 / (Q z.y : ℂ) +
        4 * s * (c : ℂ) ^ 4 * (z.y : ℂ) ^ 2 / (Q z.y : ℂ) ^ 2) z.y := by
    dsimp only [B]
    apply hBraw.congr_deriv
    push_cast
    field_simp [hQne, hy]
    ring
  have hf : HasDerivAt f (d4BMPoincareSeedVerticalFirstJet z s p) z.y := by
    exact hasDerivAt_d4BMPoincareSeed_vertical z s p
  have hprod := hBderiv.mul hf
  have hfun : d4BMPoincareSeedVerticalFirstJetSlice z s p = fun y => B y * f y := by
    funext y
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  let QC : ℂ := (Q z.y : ℂ)
  let Y : ℂ := (z.y : ℂ)
  let F : ℂ := f z.y
  have hB : B z.y = s / Y - 2 * s * (c : ℂ) ^ 2 * Y / QC := by rfl
  have hFvalue : F = d4BMPoincareSeed z s p := by rfl
  have hfirst : d4BMPoincareSeedVerticalFirstJet z s p =
      (s / Y - 2 * s * (c : ℂ) ^ 2 * Y / QC) * F := by
    rw [hFvalue]
    unfold d4BMPoincareSeedVerticalFirstJet d4BMPoincareSeed
      d4BMPoincareQuadratic
    dsimp only [c, u, QC, Y, Q, F, f, d4BMPoincareSeedVerticalSlice]
    push_cast
    rfl
  have hsecond : d4BMPoincareSeedVerticalSecondJet z s p =
      (s * (s - 1) / Y ^ 2 -
        2 * s * (1 + 2 * s) * (c : ℂ) ^ 2 / QC +
        4 * s * (s + 1) * (c : ℂ) ^ 4 * Y ^ 2 / QC ^ 2) * F := by
    rw [hFvalue]
    unfold d4BMPoincareSeedVerticalSecondJet d4BMPoincareSeed
      d4BMPoincareQuadratic
    dsimp only [c, u, QC, Y, Q, F, f, d4BMPoincareSeedVerticalSlice]
    push_cast
    rfl
  rw [hB, hfirst, hsecond]
  dsimp only [QC, Y, F]
  field_simp [hQne, hy]
  ring

theorem hasDerivAt_d4BMPoincareSeed_horizontal
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt
      (fun x : ℝ => d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p)
      (d4BMPoincareSeedHorizontalFirstJet z s p) z.x := by
  let c : ℝ := p.pair.1
  let d : ℝ := p.pair.2
  let Q : ℝ → ℝ := fun x => (c * z.y) ^ 2 + (c * x + d) ^ 2
  let r : ℝ → ℝ := fun x => z.y / Q x
  have hQpos : 0 < Q z.x := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQne : Q z.x ≠ 0 := hQpos.ne'
  have hrpos : 0 < r z.x := div_pos z.y_pos hQpos
  have hQderiv : HasDerivAt Q (2 * c * (c * z.x + d)) z.x := by
    dsimp only [Q]
    have hlin : HasDerivAt (fun x : ℝ => c * x + d) c z.x := by
      simpa using ((hasDerivAt_id z.x).const_mul c).add_const d
    exact (((hasDerivAt_const z.x (c * z.y)).pow 2).add
      (hlin.pow 2)).congr_deriv (by ring)
  have hrderiv : HasDerivAt r
      (-z.y * (2 * c * (c * z.x + d)) / (Q z.x) ^ 2) z.x := by
    dsimp only [r]
    exact ((hasDerivAt_const z.x z.y).div hQderiv hQne).congr_deriv (by ring)
  have hpow := (d4BM_hasDerivAt_ofReal_cpow s hrpos).scomp z.x hrderiv
  have hfun :
      (fun x : ℝ => d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p) =
        (fun t : ℝ => (t : ℂ) ^ s) ∘ r := by
    funext x
    rfl
  rw [hfun]
  apply hpow.congr_deriv
  let RC : ℂ := (r z.x : ℂ)
  let QC : ℂ := (Q z.x : ℂ)
  have hRCne : RC ≠ 0 := by
    dsimp only [RC]
    exact_mod_cast hrpos.ne'
  have hQCne : QC ≠ 0 := by
    dsimp only [QC]
    exact_mod_cast hQne
  have hRC : RC = (z.y : ℂ) / QC := by
    dsimp only [RC, QC, r]
    push_cast
    rfl
  have hcpow : RC ^ (s - 1) * RC = RC ^ s := by
    calc
      RC ^ (s - 1) * RC = RC ^ (s - 1) * RC ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = RC ^ ((s - 1) + 1) := (Complex.cpow_add _ _ hRCne).symm
      _ = RC ^ s := by ring_nf
  have hscalar :
      ((-z.y * (2 * c * (c * z.x + d)) / (Q z.x) ^ 2 : ℝ) : ℂ) =
        -2 * (z.y : ℂ) * (c : ℂ) * ((c : ℂ) * (z.x : ℂ) + (d : ℂ)) /
          QC ^ 2 := by
    dsimp only [QC]
    push_cast
    ring
  rw [Complex.real_smul, hscalar]
  calc
    (-2 * (z.y : ℂ) * (c : ℂ) * ((c : ℂ) * (z.x : ℂ) + (d : ℂ)) /
          QC ^ 2) * (s * RC ^ (s - 1)) =
        (-2 * s * (c : ℂ) * ((c : ℂ) * (z.x : ℂ) + (d : ℂ)) / QC) *
          (RC ^ (s - 1) * RC) := by
            rw [hRC]
            field_simp [hQCne]
    _ = (-2 * s * (c : ℂ) * ((c : ℂ) * (z.x : ℂ) + (d : ℂ)) / QC) *
          RC ^ s := by rw [hcpow]
    _ = d4BMPoincareSeedHorizontalFirstJet z s p := by
      unfold d4BMPoincareSeedHorizontalFirstJet d4BMPoincareHorizontalLinear
        d4BMPoincareSeed d4BMPoincareQuadratic
      dsimp only [c, d, QC, RC, Q, r]
      push_cast
      rfl

theorem hasDerivAt_d4BMPoincareSeedHorizontalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt
      (fun x : ℝ => d4BMPoincareSeedHorizontalFirstJet
        (d4BMHorizontalCoordinate z x) s p)
      (d4BMPoincareSeedHorizontalSecondJet z s p) z.x := by
  let c : ℝ := p.pair.1
  let d : ℝ := p.pair.2
  let Q : ℝ → ℝ := fun x => (c * z.y) ^ 2 + (c * x + d) ^ 2
  let A : ℝ → ℂ := fun x =>
    -2 * s * (c : ℂ) * ((c * x + d : ℝ) : ℂ) / (Q x : ℂ)
  let f : ℝ → ℂ := fun x =>
    d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p
  have hQpos : 0 < Q z.x := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQneR : Q z.x ≠ 0 := hQpos.ne'
  have hQne : (Q z.x : ℂ) ≠ 0 := by exact_mod_cast hQneR
  have hlinR : HasDerivAt (fun x : ℝ => c * x + d) c z.x := by
    simpa using ((hasDerivAt_id z.x).const_mul c).add_const d
  have hlin : HasDerivAt (fun x : ℝ => ((c * x + d : ℝ) : ℂ)) (c : ℂ) z.x :=
    hlinR.ofReal_comp
  have hQderivR : HasDerivAt Q (2 * c * (c * z.x + d)) z.x := by
    dsimp only [Q]
    exact (((hasDerivAt_const z.x (c * z.y)).pow 2).add
      (hlinR.pow 2)).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun x : ℝ => (Q x : ℂ))
      ((2 * c * (c * z.x + d) : ℝ) : ℂ) z.x := hQderivR.ofReal_comp
  have hAraw :=
    (hlin.const_mul (-2 * s * (c : ℂ))).div hQderiv hQne
  have hAderiv : HasDerivAt A
      (-2 * s * (c : ℂ) ^ 2 / (Q z.x : ℂ) +
        4 * s * (c : ℂ) ^ 2 * ((c * z.x + d : ℝ) : ℂ) ^ 2 /
          (Q z.x : ℂ) ^ 2) z.x := by
    dsimp only [A]
    apply hAraw.congr_deriv
    push_cast
    field_simp [hQne]
    ring
  have hf : HasDerivAt f (d4BMPoincareSeedHorizontalFirstJet z s p) z.x := by
    exact hasDerivAt_d4BMPoincareSeed_horizontal z s p
  have hprod := hAderiv.mul hf
  have hfun :
      (fun x : ℝ => d4BMPoincareSeedHorizontalFirstJet
        (d4BMHorizontalCoordinate z x) s p) = fun x => A x * f x := by
    funext x
    unfold d4BMPoincareSeedHorizontalFirstJet d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic d4BMHorizontalCoordinate
    dsimp only [A, f, Q]
    push_cast
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  let U : ℂ := ((c * z.x + d : ℝ) : ℂ)
  let QC : ℂ := (Q z.x : ℂ)
  let F : ℂ := f z.x
  have hA : A z.x = -2 * s * (c : ℂ) * U / QC := by rfl
  have hFvalue : F = d4BMPoincareSeed z s p := by
    unfold F f d4BMPoincareSeed d4BMPoincareQuadratic d4BMHorizontalCoordinate
    rfl
  have hfirst : d4BMPoincareSeedHorizontalFirstJet z s p =
      (-2 * s * (c : ℂ) * U / QC) * F := by
    rw [hFvalue]
    unfold d4BMPoincareSeedHorizontalFirstJet d4BMPoincareHorizontalLinear
      d4BMPoincareSeed d4BMPoincareQuadratic
    dsimp only [c, d, U, QC, Q, F, f]
    push_cast
    rfl
  have hsecond : d4BMPoincareSeedHorizontalSecondJet z s p =
      (-2 * s * (c : ℂ) ^ 2 / QC +
        4 * s * (s + 1) * (c : ℂ) ^ 2 * U ^ 2 / QC ^ 2) * F := by
    rw [hFvalue]
    unfold d4BMPoincareSeedHorizontalSecondJet d4BMPoincareHorizontalLinear
      d4BMPoincareSeed d4BMPoincareQuadratic
    dsimp only [c, d, U, QC, Q, F, f]
    push_cast
    rfl
  rw [hA, hfirst, hsecond]
  dsimp only [QC, U, F]
  field_simp [hQne]
  ring

theorem d4BM_poincareSeed_formalHyperbolicLaplacian_eq_eigenvalue
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    (z.y : ℂ) ^ 2 *
        (d4BMPoincareSeedHorizontalSecondJet z s p +
          d4BMPoincareSeedVerticalSecondJet z s p) =
      s * (s - 1) * d4BMPoincareSeed z s p := by
  have hQ : (d4BMPoincareQuadratic z p.pair : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero).ne'
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hdecomp :
      (d4BMPoincareQuadratic z p.pair : ℂ) =
        (p.pair.1 : ℂ) ^ 2 * (z.y : ℂ) ^ 2 +
          (d4BMPoincareHorizontalLinear z p : ℂ) ^ 2 := by
    unfold d4BMPoincareQuadratic d4BMPoincareHorizontalLinear
    push_cast
    ring
  unfold d4BMPoincareSeedHorizontalSecondJet
    d4BMPoincareSeedVerticalSecondJet
  field_simp [hQ, hy]
  rw [hdecomp]
  ring

theorem d4BM_poincareSeed_actualSecondDerivative_eigenEquation
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt
        (fun x : ℝ => d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p)
        (d4BMPoincareSeedHorizontalFirstJet z s p) z.x ∧
      HasDerivAt
        (fun x : ℝ => d4BMPoincareSeedHorizontalFirstJet
          (d4BMHorizontalCoordinate z x) s p)
        (d4BMPoincareSeedHorizontalSecondJet z s p) z.x ∧
      HasDerivAt (d4BMPoincareSeedVerticalSlice z s p)
        (d4BMPoincareSeedVerticalFirstJet z s p) z.y ∧
      HasDerivAt (d4BMPoincareSeedVerticalFirstJetSlice z s p)
        (d4BMPoincareSeedVerticalSecondJet z s p) z.y ∧
      (z.y : ℂ) ^ 2 *
          (d4BMPoincareSeedHorizontalSecondJet z s p +
            d4BMPoincareSeedVerticalSecondJet z s p) =
        s * (s - 1) * d4BMPoincareSeed z s p := by
  exact ⟨hasDerivAt_d4BMPoincareSeed_horizontal z s p,
    hasDerivAt_d4BMPoincareSeedHorizontalFirstJet_horizontal z s p,
    hasDerivAt_d4BMPoincareSeed_vertical z s p,
    hasDerivAt_d4BMPoincareSeedVerticalFirstJetSlice z s p,
    d4BM_poincareSeed_formalHyperbolicLaplacian_eq_eigenvalue z s p⟩

theorem d4BM_poincareSeed_geometricEigenvalue_centered
    (z : D4BMUpperHalfPlaneCoordinate) (u : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    (z.y : ℂ) ^ 2 *
        (d4BMPoincareSeedHorizontalSecondJet z (1 / 2 + u) p +
          d4BMPoincareSeedVerticalSecondJet z (1 / 2 + u) p) =
      thetaCuspHawkingEisensteinGeometricEigenvalue u *
        d4BMPoincareSeed z (1 / 2 + u) p := by
  rw [d4BM_poincareSeed_formalHyperbolicLaplacian_eq_eigenvalue]
  unfold thetaCuspHawkingEisensteinGeometricEigenvalue
  ring

end
end RHTower
