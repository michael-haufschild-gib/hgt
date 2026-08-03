import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaTensorSquareMateIdentification
import GaloisForLFunctions.RHTower.BilateralPrimeAnglePacketSewing
import GaloisForLFunctions.RHTower.EulerUnitTangent

/-!
# Deninger failure-nerve metric and singular Cartier landing

The normalized prime-winning face transition splits into a radial Deninger
half-density character and a local Euler gauge.  This file constructs the
finite-face metric forced by that gauge, proves its uniqueness, and identifies
the resulting source-inverse/analytic-dagger mate curvature with the existing
Deninger tensor-square curvature.

The final section proves the unconditional local analytic mechanism needed at
the cofinal Xi divisor: inverse-square metrics transport through nonzero limits,
and a zero of order `d` has a finite, positive top-conormal renormalization after
removing the exact pole of order `2*d`.

No cofinal Euler-product limit, Xi-zero location, or RH assumption is used.
-/

open Complex
open Filter Topology

namespace RHTower

noncomputable section

/-! ## Abstract finite face-gauge metric -/

/-- Product gauge carried by a finite prime face. -/
def deningerFailureNerveFaceGaugeProduct (Q : Nat.Primes → ℂ)
    (F : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ F, Q p

/-- Inverse-square Hermitian weight attached to a finite prime face. -/
def deningerFailureNerveFaceGaugeMetric (Q : Nat.Primes → ℂ)
    (F : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ F, ‖Q p‖⁻¹ ^ 2

/-- A face transition split into radial half-density and Euler gauge. -/
def deningerFailureNerveNormalizedFaceTransition
    (Q : Nat.Primes → ℂ) (depth : Nat.Primes → ℕ)
    (s : ℂ) (p : Nat.Primes) : ℂ :=
  bilateralHalfDensityCharacter ((p : ℕ) ^ depth p) s * Q p

/-- The product definition is exactly inverse squared norm of the total face
gauge, not a coordinatewise surrogate. -/
theorem deningerFailureNerveFaceGaugeMetric_eq_norm_product
    (Q : Nat.Primes → ℂ) (F : Finset Nat.Primes) :
    deningerFailureNerveFaceGaugeMetric Q F =
      ‖deningerFailureNerveFaceGaugeProduct Q F‖⁻¹ ^ 2 := by
  simp [deningerFailureNerveFaceGaugeMetric,
    deningerFailureNerveFaceGaugeProduct, norm_prod,
    Finset.prod_inv_distrib, Finset.prod_pow]

/-- Adjoining one prime multiplies the face metric by the inverse-square local
gauge. -/
theorem deningerFailureNerveFaceGaugeMetric_insert
    (Q : Nat.Primes → ℂ) (F : Finset Nat.Primes) (p : Nat.Primes)
    (hp : p ∉ F) :
    deningerFailureNerveFaceGaugeMetric Q (insert p F) =
      deningerFailureNerveFaceGaugeMetric Q F * ‖Q p‖⁻¹ ^ 2 := by
  simp [deningerFailureNerveFaceGaugeMetric, hp, mul_comm]

/-- Exact metric purification: target weight times actual transition norm is
source weight times the radial Deninger norm. -/
theorem deningerFailureNerveFaceGaugeMetric_purifies
    (Q : Nat.Primes → ℂ) (depth : Nat.Primes → ℕ) (s : ℂ)
    (F : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∉ F)
    (hQ : Q p ≠ 0) :
    deningerFailureNerveFaceGaugeMetric Q (insert p F) *
        ‖deningerFailureNerveNormalizedFaceTransition Q depth s p‖ ^ 2 =
      deningerFailureNerveFaceGaugeMetric Q F *
        ‖bilateralHalfDensityCharacter ((p : ℕ) ^ depth p) s‖ ^ 2 := by
  rw [deningerFailureNerveFaceGaugeMetric_insert Q F p hp]
  rw [deningerFailureNerveNormalizedFaceTransition, norm_mul]
  have hnorm : ‖Q p‖ ≠ 0 := norm_ne_zero_iff.mpr hQ
  field_simp

/-- Edge purification and the empty-face normalization force the diagonal
metric on every finite face.  Positivity of a competing weight is unnecessary:
the transport equations themselves already give uniqueness. -/
theorem deningerFailureNerveFaceGaugeMetric_unique
    (Q : Nat.Primes → ℂ) (depth : Nat.Primes → ℕ) (s : ℂ)
    (k : Finset Nat.Primes → ℝ)
    (hzero : k ∅ = 1)
    (hedge : ∀ (F : Finset Nat.Primes) (p : Nat.Primes), p ∉ F →
      k (insert p F) *
          ‖deningerFailureNerveNormalizedFaceTransition Q depth s p‖ ^ 2 =
        k F *
          ‖bilateralHalfDensityCharacter ((p : ℕ) ^ depth p) s‖ ^ 2)
    (hQ : ∀ p, Q p ≠ 0) :
    ∀ F, k F = deningerFailureNerveFaceGaugeMetric Q F := by
  intro F
  induction F using Finset.induction with
  | empty => simpa [deningerFailureNerveFaceGaugeMetric] using hzero
  | @insert p F hp ih =>
      have h := hedge F p hp
      rw [deningerFailureNerveNormalizedFaceTransition, norm_mul] at h
      have hrad :
          ‖bilateralHalfDensityCharacter ((p : ℕ) ^ depth p) s‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact bilateralHalfDensityCharacter_ne_zero
          (pow_pos p.2.pos _) s
      have hq : ‖Q p‖ ≠ 0 := norm_ne_zero_iff.mpr (hQ p)
      rw [deningerFailureNerveFaceGaugeMetric_insert Q F p hp]
      rw [← ih]
      field_simp at h ⊢
      nlinarith

/-! ## Actual Euler gauge and normalized prime-winning transition -/

/-- Local Euler gauge before normalization:
`G_{p,m}(s) = (1-p^{-s})/(1-p^{-(m+1)s})`. -/
def deningerFailureNerveEulerGaugeCore
    (p : Nat.Primes) (m : ℕ) (s : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (-s)) /
    (1 - (p : ℂ) ^ (-(((m + 1 : ℕ) : ℂ) * s)))

/-- The Euler gauge core is nonzero throughout the open right half-plane. -/
theorem deningerFailureNerveEulerGaugeCore_ne_zero
    (p : Nat.Primes) (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    deningerFailureNerveEulerGaugeCore p m s ≠ 0 := by
  rw [deningerFailureNerveEulerGaugeCore, div_ne_zero_iff]
  constructor
  · exact one_sub_prime_cpow_neg_ne_zero p.2.two_le hs
  · apply one_sub_prime_cpow_neg_ne_zero p.2.two_le
    rw [mul_re]
    norm_num
    exact mul_pos (by positivity) hs

/-- At the normalization point, the complex Euler core is the expected ratio
of inverse prime powers. -/
theorem deningerFailureNerveEulerGaugeCore_one_eq
    (p : Nat.Primes) (m : ℕ) :
    deningerFailureNerveEulerGaugeCore p m 1 =
      (1 - (p : ℂ)⁻¹) / (1 - ((p : ℂ) ^ (m + 1))⁻¹) := by
  rw [deningerFailureNerveEulerGaugeCore]
  rw [show (-((1 : ℂ)) : ℂ) = -1 by rfl,
    Complex.cpow_neg_one]
  rw [show -(((m + 1 : ℕ) : ℂ) * (1 : ℂ)) =
    -(((m + 1 : ℕ) : ℂ)) by ring]
  rw [Complex.cpow_neg, Complex.cpow_natCast]

/-- The normalization-point Euler core lies on the positive real ray. -/
theorem deningerFailureNerveEulerGaugeCore_one_eq_real
    (p : Nat.Primes) (m : ℕ) :
    deningerFailureNerveEulerGaugeCore p m 1 =
      (((1 - (p : ℝ)⁻¹) /
        (1 - ((p : ℝ) ^ (m + 1))⁻¹) : ℝ) : ℂ) := by
  rw [deningerFailureNerveEulerGaugeCore_one_eq]
  push_cast
  rfl

/-- Positivity of the actual real normalization ratio. -/
theorem deningerFailureNerveEulerGaugeCore_one_real_pos
    (p : Nat.Primes) (m : ℕ) :
    0 < (1 - (p : ℝ)⁻¹) /
      (1 - ((p : ℝ) ^ (m + 1))⁻¹) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hpPow : (1 : ℝ) < (p : ℝ) ^ (m + 1) :=
    one_lt_pow₀ hpR (Nat.succ_ne_zero m)
  exact div_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR))
    (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpPow))

/-- Positive square-root normalization of the local Euler gauge. -/
def deningerFailureNerveEulerGaugeNormalizer
    (p : Nat.Primes) (m : ℕ) : ℝ :=
  Real.sqrt ‖deningerFailureNerveEulerGaugeCore p m 1‖

/-- The Euler normalizer is strictly positive. -/
theorem deningerFailureNerveEulerGaugeNormalizer_pos
    (p : Nat.Primes) (m : ℕ) :
    0 < deningerFailureNerveEulerGaugeNormalizer p m := by
  rw [deningerFailureNerveEulerGaugeNormalizer, Real.sqrt_pos]
  exact norm_pos_iff.mpr
    (deningerFailureNerveEulerGaugeCore_ne_zero p m 1 (by norm_num))

/-- The norm-based positive square root is exactly the paper normalization
`sqrt G_{p,m}(1)`. -/
theorem deningerFailureNerveEulerGaugeNormalizer_eq_actual
    (p : Nat.Primes) (m : ℕ) :
    deningerFailureNerveEulerGaugeNormalizer p m =
      Real.sqrt ((1 - (p : ℝ)⁻¹) /
        (1 - ((p : ℝ) ^ (m + 1))⁻¹)) := by
  rw [deningerFailureNerveEulerGaugeNormalizer,
    deningerFailureNerveEulerGaugeCore_one_eq_real,
    norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerFailureNerveEulerGaugeCore_one_real_pos p m)]

/-- Actual normalized Euler face gauge
`Q_{p,m}(s) = G_{p,m}(s)/sqrt(G_{p,m}(1))`. -/
def deningerFailureNerveEulerGauge
    (p : Nat.Primes) (m : ℕ) (s : ℂ) : ℂ :=
  deningerFailureNerveEulerGaugeCore p m s /
    deningerFailureNerveEulerGaugeNormalizer p m

/-- The normalized Euler gauge is nonzero on the open right half-plane. -/
theorem deningerFailureNerveEulerGauge_ne_zero
    (p : Nat.Primes) (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    deningerFailureNerveEulerGauge p m s ≠ 0 := by
  rw [deningerFailureNerveEulerGauge, div_ne_zero_iff]
  exact ⟨deningerFailureNerveEulerGaugeCore_ne_zero p m s hs,
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (deningerFailureNerveEulerGaugeNormalizer_pos p m))⟩

/-- Prime-power half-density is exactly the radial factor
`p^{-m(s-1/2)}` appearing in the normalized face transition. -/
theorem deningerFailureNerveHalfDensity_primePower_eq
    (p : Nat.Primes) (m : ℕ) (s : ℂ) :
    bilateralHalfDensityCharacter ((p : ℕ) ^ m) s =
      (p : ℂ) ^ (-(((m : ℕ) : ℂ) * (s - (1 / 2 : ℂ)))) := by
  rw [bilateralHalfDensityCharacter, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul]
  congr 1
  push_cast
  ring

/-- Total actual Euler gauge on a finite failure-nerve face. -/
def deningerFailureNerveActualFaceGaugeProduct
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) : ℂ :=
  deningerFailureNerveFaceGaugeProduct
    (fun p => deningerFailureNerveEulerGauge p m s) F

/-- Forced inverse-square metric on the actual finite failure nerve. -/
def deningerFailureNerveActualFaceMetric
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) : ℝ :=
  deningerFailureNerveFaceGaugeMetric
    (fun p => deningerFailureNerveEulerGauge p m s) F

/-- Actual normalized prime-winning face transition. -/
def deningerFailureNerveActualTransition
    (m : ℕ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  bilateralHalfDensityCharacter ((p : ℕ) ^ m) s *
    deningerFailureNerveEulerGauge p m s

/-- The constructed transition is exactly
`p^{-m(s-1/2)} Q_{p,m}(s)`. -/
theorem deningerFailureNerveActualTransition_eq_normalized_face_formula
    (m : ℕ) (s : ℂ) (p : Nat.Primes) :
    deningerFailureNerveActualTransition m s p =
      (p : ℂ) ^ (-(((m : ℕ) : ℂ) * (s - (1 / 2 : ℂ)))) *
        deningerFailureNerveEulerGauge p m s := by
  rw [deningerFailureNerveActualTransition,
    deningerFailureNerveHalfDensity_primePower_eq]

/-- The actual face metric is inverse squared norm of the full Čech gauge
product. -/
theorem deningerFailureNerveActualFaceMetric_eq_norm_product
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) :
    deningerFailureNerveActualFaceMetric m s F =
      ‖deningerFailureNerveActualFaceGaugeProduct m s F‖⁻¹ ^ 2 := by
  exact deningerFailureNerveFaceGaugeMetric_eq_norm_product
    (fun p => deningerFailureNerveEulerGauge p m s) F

/-- The forced actual face metric is strictly positive in the right
half-plane. -/
theorem deningerFailureNerveActualFaceMetric_pos
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) (hs : 0 < s.re) :
    0 < deningerFailureNerveActualFaceMetric m s F := by
  rw [deningerFailureNerveActualFaceMetric,
    deningerFailureNerveFaceGaugeMetric]
  apply Finset.prod_pos
  intro p hp
  positivity [norm_pos_iff.mpr
    (deningerFailureNerveEulerGauge_ne_zero p m s hs)]

/-- Exact purification of every actual finite face edge. -/
theorem deningerFailureNerveActualFaceMetric_purifies
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) (p : Nat.Primes)
    (hp : p ∉ F) (hs : 0 < s.re) :
    deningerFailureNerveActualFaceMetric m s (insert p F) *
        ‖deningerFailureNerveActualTransition m s p‖ ^ 2 =
      deningerFailureNerveActualFaceMetric m s F *
        ‖bilateralHalfDensityCharacter ((p : ℕ) ^ m) s‖ ^ 2 := by
  exact deningerFailureNerveFaceGaugeMetric_purifies
    (fun q => deningerFailureNerveEulerGauge q m s)
    (fun _ => m) s F p hp
    (deningerFailureNerveEulerGauge_ne_zero p m s hs)

/-- The actual finite source metric is the unique diagonal metric normalized
at the empty face that purifies all actual transitions. -/
theorem deningerFailureNerveActualFaceMetric_unique
    (m : ℕ) (s : ℂ) (k : Finset Nat.Primes → ℝ)
    (hzero : k ∅ = 1)
    (hedge : ∀ (F : Finset Nat.Primes) (p : Nat.Primes), p ∉ F →
      k (insert p F) *
          ‖deningerFailureNerveActualTransition m s p‖ ^ 2 =
        k F *
          ‖bilateralHalfDensityCharacter ((p : ℕ) ^ m) s‖ ^ 2)
    (hs : 0 < s.re) :
    ∀ F, k F = deningerFailureNerveActualFaceMetric m s F := by
  exact deningerFailureNerveFaceGaugeMetric_unique
    (fun p => deningerFailureNerveEulerGauge p m s)
    (fun _ => m) s k hzero hedge
    (fun p => deningerFailureNerveEulerGauge_ne_zero p m s hs)

/-! ## Purified incidence gain and Deninger mate curvature -/

/-- Squared incidence gain measured between source and target face metrics. -/
def deningerFailureNerveActualPurifiedSquaredGain
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) (p : Nat.Primes) : ℝ :=
  deningerFailureNerveActualFaceMetric m s (insert p F) *
      ‖deningerFailureNerveActualTransition m s p‖ ^ 2 /
    deningerFailureNerveActualFaceMetric m s F

/-- Purification removes precisely the Euler gauge and leaves radial squared
gain. -/
theorem deningerFailureNerveActualPurifiedSquaredGain_eq
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) (p : Nat.Primes)
    (hp : p ∉ F) (hs : 0 < s.re) :
    deningerFailureNerveActualPurifiedSquaredGain m s F p =
      ‖bilateralHalfDensityCharacter ((p : ℕ) ^ m) s‖ ^ 2 := by
  rw [deningerFailureNerveActualPurifiedSquaredGain,
    deningerFailureNerveActualFaceMetric_purifies m s F p hp hs]
  exact mul_div_cancel_left₀ _
    (ne_of_gt (deningerFailureNerveActualFaceMetric_pos m s F hs))

/-- Source-inverse/analytic-dagger mate curvature of a purified face edge. -/
def deningerFailureNerveActualPurifiedMateCurvature
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) (p : Nat.Primes) : ℝ :=
  (deningerFailureNerveActualPurifiedSquaredGain m s F p)⁻¹ -
    deningerFailureNerveActualPurifiedSquaredGain m s F p

/-- **Finite failure-nerve/Deninger curvature identification.**  Curvature of
the uniquely purified actual face edge is exactly tensor-square radial mate
curvature at degree `p^m`. -/
theorem deningerFailureNerveActualPurifiedMateCurvature_eq
    (m : ℕ) (s : ℂ) (F : Finset Nat.Primes) (p : Nat.Primes)
    (hp : p ∉ F) (hs : 0 < s.re) :
    deningerFailureNerveActualPurifiedMateCurvature m s F p =
      deningerTensorSquareRadialMateCurvature ((p : ℕ) ^ m) s := by
  rw [deningerFailureNerveActualPurifiedMateCurvature,
    deningerFailureNerveActualPurifiedSquaredGain_eq m s F p hp hs,
    deningerTensorSquareRadialMateCurvature]
  rw [inv_pow]

/-! ## Inverse-square limit transport and singular Cartier renormalization -/

/-- A nonzero complex limit transports through norm, inversion, and squaring. -/
theorem tendsto_norm_inverse_square
    {α : Type*} [TopologicalSpace α] {l : Filter α}
    {q : α → ℂ} {z : ℂ}
    (hq : Tendsto q l (𝓝 z)) (hz : z ≠ 0) :
    Tendsto (fun x => ‖q x‖⁻¹ ^ 2) l (𝓝 (‖z‖⁻¹ ^ 2)) := by
  exact (hq.norm.inv₀ (norm_ne_zero_iff.mpr hz)).pow 2

/-- Singular inverse-square Hermitian metric associated with a local defining
function. -/
def deningerCartierInverseSquareMetric
    (weight : ℝ) (f : ℂ → ℂ) (u : ℂ) : ℝ :=
  weight * ‖f u‖⁻¹ ^ 2

/-- Top-conormal renormalization for a zero of analytic order `d`. -/
def deningerCartierConormalRenormalization
    (weight : ℝ) (f : ℂ → ℂ) (rho : ℂ) (d : ℕ) (u : ℂ) : ℝ :=
  ‖u - rho‖ ^ (2 * d) * deningerCartierInverseSquareMetric weight f u

/-- Exact punctured factorization: a zero of order `d` creates inverse-square
pole order `2*d`, completely removed by top-conormal renormalization. -/
theorem deningerCartierConormalRenormalization_eq
    (weight : ℝ) (f g : ℂ → ℂ) (rho u : ℂ) (d : ℕ)
    (hu : u ≠ rho) (hgu : g u ≠ 0)
    (hf : f u = (u - rho) ^ d * g u) :
    deningerCartierConormalRenormalization weight f rho d u =
      weight * ‖g u‖⁻¹ ^ 2 := by
  rw [deningerCartierConormalRenormalization,
    deningerCartierInverseSquareMetric, hf, norm_mul, norm_pow]
  have hur : ‖u - rho‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hu)
  have hgr : ‖g u‖ ≠ 0 := norm_ne_zero_iff.mpr hgu
  field_simp
  ring

/-- Multiplicity-exact local Cartier landing: if the residual factor tends to
a nonzero value, conormal renormalization tends to its finite inverse-square
metric. -/
theorem deningerCartierConormalRenormalization_tendsto
    (weight : ℝ) (f g : ℂ → ℂ) (rho c : ℂ) (d : ℕ)
    (hf : ∀ᶠ u in 𝓝[≠] rho, f u = (u - rho) ^ d * g u)
    (hg : Tendsto g (𝓝[≠] rho) (𝓝 c)) (hc : c ≠ 0) :
    Tendsto (deningerCartierConormalRenormalization weight f rho d)
      (𝓝[≠] rho) (𝓝 (weight * ‖c‖⁻¹ ^ 2)) := by
  have hgne : ∀ᶠ u in 𝓝[≠] rho, g u ≠ 0 := hg.eventually_ne hc
  have hune : ∀ᶠ u in 𝓝[≠] rho, u ≠ rho := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa using hu
  apply (tendsto_const_nhds.mul
    (tendsto_norm_inverse_square hg hc)).congr'
  filter_upwards [hf, hgne, hune] with u hfu hgu hu
  exact (deningerCartierConormalRenormalization_eq
    weight f g rho u d hu hgu hfu).symm

/-- The conormal landing is strictly positive for positive source weight and
nonzero residual Cartier coefficient. -/
theorem deningerCartierConormalRenormalization_limit_pos
    (weight : ℝ) (c : ℂ) (hweight : 0 < weight) (hc : c ≠ 0) :
    0 < weight * ‖c‖⁻¹ ^ 2 := by
  positivity [norm_pos_iff.mpr hc]

end

end RHTower
