import GaloisForLFunctions.RHTower.RealPrincipalSeriesDiagonalDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Diagonal infinitesimal action on compact principal-series K-types

This file computes the Iwasawa coordinates of `k · diag(exp t, exp (-t))` for arbitrary
`k ∈ K`, differentiates both the Borel scale and compact phase, and proves pointwise on every
finite spherical K-type that the inverse diagonal flow in inducing exponent `1 - s` is the
transported Harish-Chandra operator `E + F`.
-/

namespace GaloisForLFunctions.RHTower

open Matrix

noncomputable section

theorem hasDerivAt_zpow_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (n : ℤ) (hx : f x ≠ 0) :
    HasDerivAt (fun t => f t ^ n)
      ((n : ℂ) * f x ^ (n - 1) * f') x := by
  cases n with
  | ofNat n =>
      cases n with
      | zero => simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ)))
      | succ n =>
          convert! hf.pow (n + 1) using 1
          simp
  | negSucc n =>
      have h := (hf.inv hx).pow (n + 1)
      convert! h using 1
      · ext t
        simp [zpow_negSucc]
      · simp [zpow_negSucc]
        field_simp
        ring

theorem realIwasawaB_zero_zero (g : SL2R) :
    ((realIwasawaB g : realUpperBorel) : SL2R) 0 0 =
      Real.sqrt (1 / (g 1 0 ^ 2 + g 1 1 ^ 2)) := by
  change Real.sqrt ((g • UpperHalfPlane.I).im) = _
  have him : (g • UpperHalfPlane.I).im =
      1 / (g 1 0 ^ 2 + g 1 1 ^ 2) := by
    change ((g.mapGL ℝ) • UpperHalfPlane.I).im = _
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp [UpperHalfPlane.denom, Complex.normSq_apply]
    ring
  rw [him]

theorem realIwasawaK_phase (g : SL2R) :
    realSphericalKPhase (realIwasawaK g) =
      (((realIwasawaB g : realUpperBorel) : SL2R) 0 0 : ℂ) *
        ((g 1 1 : ℂ) + Complex.I * (g 1 0 : ℂ)) := by
  let b := realIwasawaB g
  let q := realIwasawaK g
  have hb10 : (b : SL2R) 1 0 = 0 := b.property
  have hdet := (b : SL2R).property
  rw [Matrix.det_fin_two, hb10] at hdet
  have hbdiag : (b : SL2R) 0 0 * (b : SL2R) 1 1 = 1 := by
    simpa using hdet
  have hprod := realIwasawaB_mul_realIwasawaK g
  have h10 := congrArg (fun x : SL2R => (x : Matrix (Fin 2) (Fin 2) ℝ) 1 0) hprod
  have h11 := congrArg (fun x : SL2R => (x : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hprod
  change ((b : SL2R) * (q : SL2R)) 1 0 = g 1 0 at h10
  change ((b : SL2R) * (q : SL2R)) 1 1 = g 1 1 at h11
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] at h10 h11
  simp only [hb10, zero_mul, zero_add] at h10 h11
  rcases upperHalfPlaneStabilizer_matrix_relations q with ⟨hq10, hq11⟩
  have hq10' : (b : SL2R) 0 0 * g 1 0 = (q : SL2R) 1 0 := by
    calc
      _ = (b : SL2R) 0 0 * ((b : SL2R) 1 1 * (q : SL2R) 1 0) := by rw [h10]
      _ = ((b : SL2R) 0 0 * (b : SL2R) 1 1) * (q : SL2R) 1 0 := by ring
      _ = _ := by rw [hbdiag, one_mul]
  have hq11' : (b : SL2R) 0 0 * g 1 1 = (q : SL2R) 1 1 := by
    calc
      _ = (b : SL2R) 0 0 * ((b : SL2R) 1 1 * (q : SL2R) 1 1) := by rw [h11]
      _ = ((b : SL2R) 0 0 * (b : SL2R) 1 1) * (q : SL2R) 1 1 := by ring
      _ = _ := by rw [hbdiag, one_mul]
  change realSphericalKPhase q =
    (((b : realUpperBorel) : SL2R) 0 0 : ℂ) *
      ((g 1 1 : ℂ) + Complex.I * (g 1 0 : ℂ))
  simp only [realSphericalKPhase]
  rw [← hq11, show (q : SL2R) 0 1 = -(q : SL2R) 1 0 by linarith]
  push_cast
  have hq10c : (((q : SL2R) 1 0 : ℝ) : ℂ) =
      (((b : SL2R) 0 0 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by
    exact_mod_cast hq10'.symm
  have hq11c : (((q : SL2R) 1 1 : ℝ) : ℂ) =
      (((b : SL2R) 0 0 : ℝ) : ℂ) * ((g 1 1 : ℝ) : ℂ) := by
    exact_mod_cast hq11'.symm
  rw [hq10c, hq11c]
  ring

theorem sphericalK_lower_row_normSq (k : upperHalfPlaneStabilizer) :
    (k : SL2R) 1 0 ^ 2 + (k : SL2R) 1 1 ^ 2 = 1 := by
  have h := realSphericalKPhase_normSq k
  rcases upperHalfPlaneStabilizer_matrix_relations k with ⟨hk10, hk11⟩
  simp [realSphericalKPhase, Complex.normSq_apply] at h
  rw [hk10, hk11]
  nlinarith

def realDiagonalIwasawaNormSq (k : upperHalfPlaneStabilizer) (t : ℝ) : ℝ :=
  ((k : SL2R) 1 0 * Real.exp t) ^ 2 +
    ((k : SL2R) 1 1 * Real.exp (-t)) ^ 2

def realDiagonalIwasawaScale (k : upperHalfPlaneStabilizer) (t : ℝ) : ℝ :=
  Real.sqrt (1 / realDiagonalIwasawaNormSq k t)

def realDiagonalIwasawaPhase (k : upperHalfPlaneStabilizer) (t : ℝ) : ℂ :=
  (realDiagonalIwasawaScale k t : ℂ) *
    ((((k : SL2R) 1 1 * Real.exp (-t) : ℝ) : ℂ) +
      Complex.I * (((k : SL2R) 1 0 * Real.exp t : ℝ) : ℂ))

@[simp]
theorem realDiagonalIwasawaScale_zero (k : upperHalfPlaneStabilizer) :
    realDiagonalIwasawaScale k 0 = 1 := by
  simp [realDiagonalIwasawaScale, realDiagonalIwasawaNormSq, sphericalK_lower_row_normSq]

@[simp]
theorem realDiagonalIwasawaPhase_zero (k : upperHalfPlaneStabilizer) :
    realDiagonalIwasawaPhase k 0 = realSphericalKPhase k := by
  rcases upperHalfPlaneStabilizer_matrix_relations k with ⟨hk10, hk11⟩
  simp [realDiagonalIwasawaPhase, realSphericalKPhase, hk10, hk11]
  ring

theorem realIwasawaB_rotation_diagonal (k : upperHalfPlaneStabilizer) (t : ℝ) :
    ((realIwasawaB ((k : SL2R) * (realPositiveDiagonalBorel t : SL2R)) :
      realUpperBorel) : SL2R) 0 0 = realDiagonalIwasawaScale k t := by
  rw [realIwasawaB_zero_zero]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, realPositiveDiagonalBorel]
  simp [realDiagonalIwasawaScale, realDiagonalIwasawaNormSq]

theorem realIwasawaK_phase_rotation_diagonal
    (k : upperHalfPlaneStabilizer) (t : ℝ) :
    realSphericalKPhase
        (realIwasawaK ((k : SL2R) * (realPositiveDiagonalBorel t : SL2R))) =
      realDiagonalIwasawaPhase k t := by
  rw [realIwasawaK_phase, realIwasawaB_rotation_diagonal]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, realPositiveDiagonalBorel]
  simp [realDiagonalIwasawaPhase]

@[simp]
theorem realDiagonalIwasawaNormSq_zero (k : upperHalfPlaneStabilizer) :
    realDiagonalIwasawaNormSq k 0 = 1 := by
  simp [realDiagonalIwasawaNormSq, sphericalK_lower_row_normSq]

theorem hasDerivAt_realDiagonalIwasawaNormSq (k : upperHalfPlaneStabilizer) :
    HasDerivAt (realDiagonalIwasawaNormSq k)
      (2 * ((k : SL2R) 1 0 ^ 2 - (k : SL2R) 1 1 ^ 2)) 0 := by
  let c := (k : SL2R) 1 0
  let d := (k : SL2R) 1 1
  have hc := (Real.hasDerivAt_exp 0).const_mul c
  have hneg := (hasDerivAt_id (0 : ℝ)).neg
  have hd := ((Real.hasDerivAt_exp (-0)).comp 0 hneg).const_mul d
  have h := (hc.pow 2).add (hd.pow 2)
  convert! h using 1
  simp [c, d]
  ring

theorem hasDerivAt_realDiagonalIwasawaScale (k : upperHalfPlaneStabilizer) :
    HasDerivAt (realDiagonalIwasawaScale k)
      ((k : SL2R) 1 1 ^ 2 - (k : SL2R) 1 0 ^ 2) 0 := by
  have hnorm := hasDerivAt_realDiagonalIwasawaNormSq k
  have hinv := hnorm.inv (by simp)
  have hsqrt := hinv.sqrt (by simp)
  convert hsqrt using 1
  · ext t
    simp [realDiagonalIwasawaScale]
  · simp
    ring

private theorem complexDiagonalPhaseAlgebra (c d : ℂ)
    (h : c ^ 2 + d ^ 2 = 1) :
    2 * Complex.I * c * d * (d + Complex.I * c) =
      (d ^ 2 - c ^ 2) * (d + Complex.I * c) + (-d + Complex.I * c) := by
  rw [show -d + Complex.I * c = -(d - Complex.I * c) by ring]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  linear_combination (-d + Complex.I * c) * h

theorem hasDerivAt_realDiagonalIwasawaPhase (k : upperHalfPlaneStabilizer) :
    HasDerivAt (realDiagonalIwasawaPhase k)
      (2 * Complex.I * ((k : SL2R) 1 0 : ℂ) * ((k : SL2R) 1 1 : ℂ) *
        realSphericalKPhase k) 0 := by
  let c := (k : SL2R) 1 0
  let d := (k : SL2R) 1 1
  have hscaleR := hasDerivAt_realDiagonalIwasawaScale k
  have hscale : HasDerivAt (fun t : ℝ => (realDiagonalIwasawaScale k t : ℂ))
      ((d ^ 2 - c ^ 2 : ℝ) : ℂ) 0 := by
    simpa [c, d] using hscaleR.ofReal_comp
  have hneg := (hasDerivAt_id (0 : ℝ)).neg
  have hdR := ((Real.hasDerivAt_exp (-0)).comp 0 hneg).const_mul d
  have hcR := (Real.hasDerivAt_exp 0).const_mul c
  have hinside : HasDerivAt
      (fun t : ℝ => ((d * Real.exp (-t) : ℝ) : ℂ) +
        Complex.I * ((c * Real.exp t : ℝ) : ℂ))
      ((-d : ℝ) + Complex.I * (c : ℂ)) 0 := by
    convert! hdR.ofReal_comp.add (hcR.ofReal_comp.const_mul Complex.I) using 1
    norm_num
  have h := hscale.mul hinside
  convert! h using 1
  simp only [Real.exp_zero, mul_one, neg_zero, realDiagonalIwasawaScale_zero]
  rcases upperHalfPlaneStabilizer_matrix_relations k with ⟨hk10, hk11⟩
  have hphase : realSphericalKPhase k = (d : ℂ) + Complex.I * (c : ℂ) := by
    simp [realSphericalKPhase, c, d, hk10, hk11]
    ring
  rw [hphase]
  have hnormR := sphericalK_lower_row_normSq k
  have hnormC : (c : ℂ) ^ 2 + (d : ℂ) ^ 2 = 1 := by
    exact_mod_cast hnormR
  simpa [c, d] using complexDiagonalPhaseAlgebra (c : ℂ) (d : ℂ) hnormC

theorem compactRealPrincipalSeries_diagonal_KType_apply
    (σ : ℝ) (m : ℤ) (t : ℝ) (k : upperHalfPlaneStabilizer) :
    ((compactRealPrincipalSeries σ (realPositiveDiagonalBorel t : SL2R))
      (realCompactKType σ m)).1 k =
      ((realDiagonalIwasawaScale k t ^ σ : ℝ) : ℂ) *
        realDiagonalIwasawaPhase k t ^ (2 * m) := by
  rw [compactRealPrincipalSeries_apply]
  change
    ((|((realIwasawaB ((k : SL2R) *
        (realPositiveDiagonalBorel t : SL2R)) : realUpperBorel) : SL2R) 0 0| ^ σ : ℝ) : ℂ) *
      realSphericalKPhase
        (realIwasawaK ((k : SL2R) * (realPositiveDiagonalBorel t : SL2R))) ^ (2 * m) = _
  rw [realIwasawaB_rotation_diagonal,
    realIwasawaK_phase_rotation_diagonal]
  have hs : 0 ≤ realDiagonalIwasawaScale k t := Real.sqrt_nonneg _
  rw [abs_of_nonneg hs]

theorem realSphericalKPhase_ne_zero (k : upperHalfPlaneStabilizer) :
    realSphericalKPhase k ≠ 0 := by
  intro h
  have := realSphericalKPhase_normSq k
  simp [h] at this

theorem hasDerivAt_compactRealPrincipalSeries_diagonal_KType
    (σ : ℝ) (m : ℤ) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries σ (realPositiveDiagonalBorel t : SL2R))
          (realCompactKType σ m)).1 k)
      (((σ : ℂ) *
          (((k : SL2R) 1 1 : ℂ) ^ 2 - ((k : SL2R) 1 0 : ℂ) ^ 2) +
        4 * (m : ℂ) * Complex.I * ((k : SL2R) 1 0 : ℂ) *
          ((k : SL2R) 1 1 : ℂ)) *
        realSphericalKTypeCharacter m k) 0 := by
  let c := (k : SL2R) 1 0
  let d := (k : SL2R) 1 1
  let p := realSphericalKPhase k
  have hscale := hasDerivAt_realDiagonalIwasawaScale k
  have hscalarR := hscale.rpow_const (p := σ) (Or.inl (by simp))
  have hscalar : HasDerivAt
      (fun t : ℝ => ((realDiagonalIwasawaScale k t ^ σ : ℝ) : ℂ))
      (((d ^ 2 - c ^ 2) * σ : ℝ) : ℂ) 0 := by
    convert! hscalarR.ofReal_comp using 1
    simp [realDiagonalIwasawaScale_zero, c, d]
  have hphase := hasDerivAt_realDiagonalIwasawaPhase k
  have hp : p ≠ 0 := realSphericalKPhase_ne_zero k
  have hp0 : realDiagonalIwasawaPhase k 0 ≠ 0 := by simpa [p] using hp
  have hpower := hasDerivAt_zpow_comp hphase (2 * m) hp0
  have hproduct := hscalar.mul hpower
  rw [show (fun t : ℝ =>
      ((compactRealPrincipalSeries σ (realPositiveDiagonalBorel t : SL2R))
        (realCompactKType σ m)).1 k) =
      (fun t : ℝ => ((realDiagonalIwasawaScale k t ^ σ : ℝ) : ℂ) *
        realDiagonalIwasawaPhase k t ^ (2 * m)) by
    funext t
    exact compactRealPrincipalSeries_diagonal_KType_apply σ m t k]
  convert! hproduct using 1
  simp [realDiagonalIwasawaScale_zero, realDiagonalIwasawaPhase_zero,
    realSphericalKTypeCharacter_apply]
  change
    ((σ : ℂ) * ((d : ℂ) ^ 2 - (c : ℂ) ^ 2) +
      4 * (m : ℂ) * Complex.I * (c : ℂ) * (d : ℂ)) * p ^ (2 * m) =
    (((d : ℂ) ^ 2 - (c : ℂ) ^ 2) * (σ : ℂ) * p ^ (2 * m) +
      2 * (m : ℂ) * p ^ (2 * m - 1) *
        (2 * Complex.I * (c : ℂ) * (d : ℂ) * p))
  rw [show 2 * (m : ℂ) * p ^ (2 * m - 1) *
      (2 * Complex.I * (c : ℂ) * (d : ℂ) * p) =
      4 * (m : ℂ) * Complex.I * (c : ℂ) * (d : ℂ) *
        (p ^ (2 * m - 1) * p) by ring]
  rw [show p ^ (2 * m - 1) * p = p ^ (2 * m) by
    rw [← zpow_add_one₀ hp]
    congr 1
    ring]
  ring

private theorem sphericalEaddF_phase_identity (s : ℂ) (m : ℤ) (c d p : ℂ)
    (hp : p ≠ 0) (hphase : p = d + Complex.I * c)
    (hnorm : c ^ 2 + d ^ 2 = 1) :
    ((s - 1 - 2 * (m : ℂ)) / 2) * p ^ (2 * m + 2) +
        ((s - 1 + 2 * (m : ℂ)) / 2) * p ^ (2 * m - 2) =
      ((s - 1) * (d ^ 2 - c ^ 2) -
          4 * (m : ℂ) * Complex.I * c * d) * p ^ (2 * m) := by
  have hinvmul : p * (d - Complex.I * c) = 1 := by
    rw [hphase]
    ring_nf
    rw [Complex.I_sq]
    linear_combination hnorm
  have hinv : p⁻¹ = d - Complex.I * c :=
    inv_eq_of_mul_eq_one_right hinvmul
  have hneg2 : p ^ (-2 : ℤ) = (d - Complex.I * c) ^ 2 := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg]
    calc
      (p ^ 2)⁻¹ = (p⁻¹) ^ 2 := (inv_pow p 2).symm
      _ = _ := by rw [hinv]
  have hpos2 : p ^ (2 : ℤ) = (d + Complex.I * c) ^ 2 := by
    rw [hphase]
    rfl
  rw [show 2 * m + 2 = 2 * m + (2 : ℤ) by ring, zpow_add₀ hp,
    show 2 * m - 2 = 2 * m + (-2 : ℤ) by ring, zpow_add₀ hp]
  rw [hneg2, hpos2]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- The inverse positive-diagonal flow differentiates to `E + F` on every compact K-type. -/
theorem negativeDiagonal_matches_spherical_E_add_F
    (s : ℝ) (m : ℤ) (z : ℂ) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries (1 - s)
          (realPositiveDiagonalBorel (-t) : SL2R))
          (realCompactKFiniteEmbedding (1 - s) (Finsupp.single m z))).1 k)
      ((realCompactKFiniteEmbedding (1 - s)
        ((sphericalPrincipalE (s : ℂ) + sphericalPrincipalF (s : ℂ))
          (Finsupp.single m z))).1 k) 0 := by
  let c : ℂ := ((k : SL2R) 1 0 : ℂ)
  let d : ℂ := ((k : SL2R) 1 1 : ℂ)
  let p : ℂ := realSphericalKPhase k
  have hpos :=
    hasDerivAt_compactRealPrincipalSeries_diagonal_KType (1 - s) m k
  have hpos' : HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries (1 - s)
          (realPositiveDiagonalBorel t : SL2R))
          (realCompactKType (1 - s) m)).1 k)
      ((((1 - s : ℝ) : ℂ) *
          (((k : SL2R) 1 1 : ℂ) ^ 2 - ((k : SL2R) 1 0 : ℂ) ^ 2) +
        4 * (m : ℂ) * Complex.I * ((k : SL2R) 1 0 : ℂ) *
          ((k : SL2R) 1 1 : ℂ)) *
        realSphericalKTypeCharacter m k) (-0) := by
    simpa only [neg_zero] using hpos
  have hinner : HasDerivAt (fun t : ℝ => -t) (-1) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).neg using 1
  have hneg := hpos'.hasFDerivAt.comp_hasDerivAt 0 hinner
  have hz := hneg.const_mul z
  rw [show (fun t : ℝ =>
      ((compactRealPrincipalSeries (1 - s)
        (realPositiveDiagonalBorel (-t) : SL2R))
        (realCompactKFiniteEmbedding (1 - s) (Finsupp.single m z))).1 k) =
      (fun t : ℝ => z *
        ((compactRealPrincipalSeries (1 - s)
          (realPositiveDiagonalBorel (-t) : SL2R))
          (realCompactKType (1 - s) m)).1 k) by
    funext t
    rw [realCompactKFiniteEmbedding_single, map_smul]
    rfl]
  convert! hz using 1
  simp only [LinearMap.add_apply, sphericalPrincipalE_single,
    sphericalPrincipalF_single, map_add, realCompactKFiniteEmbedding_single,
    AddMemClass.coe_add, Pi.add_apply, SetLike.val_smul, Pi.smul_apply,
    smul_eq_mul, realCompactKType_apply, realSphericalKTypeCharacter_apply]
  have hp : p ≠ 0 := realSphericalKPhase_ne_zero k
  have hphase : p = d + Complex.I * c := by
    rcases upperHalfPlaneStabilizer_matrix_relations k with ⟨hk10, hk11⟩
    simp [p, d, c, realSphericalKPhase, hk10, hk11]
    ring
  have hnormR := sphericalK_lower_row_normSq k
  have hnorm : c ^ 2 + d ^ 2 = 1 := by
    dsimp [c, d]
    exact_mod_cast hnormR
  have halg := sphericalEaddF_phase_identity (s : ℂ) m c d p hp hphase hnorm
  dsimp [c, d, p] at halg ⊢
  push_cast at halg ⊢
  rw [show 2 * (m + 1) = 2 * m + 2 by ring,
    show 2 * (m - 1) = 2 * m - 2 by ring]
  linear_combination z * halg

/-- On every basis K-type, the inverse diagonal flow differentiates pointwise to the transported
compact-picture operator `E + F`. -/
theorem compactNegativeDiagonal_hasDerivAt_eq_E_add_F_single
    (s : ℝ) (m : ℤ) (z : ℂ) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries (1 - s)
          (realPositiveDiagonalBorel (-t) : SL2R))
          (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z))).1 k)
      (((compactSphericalPrincipalE s + compactSphericalPrincipalF s)
        (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z))).1.1 k) 0 := by
  rw [sphericalModelCompactKFiniteEquiv_apply_coe]
  convert negativeDiagonal_matches_spherical_E_add_F s m z k using 1
  simp only [LinearMap.add_apply, compactSphericalPrincipalE_equiv_apply,
    compactSphericalPrincipalF_equiv_apply, ← map_add,
    sphericalModelCompactKFiniteEquiv_apply_coe]

end
end GaloisForLFunctions.RHTower
