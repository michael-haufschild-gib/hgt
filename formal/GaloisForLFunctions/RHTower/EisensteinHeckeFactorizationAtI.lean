import GaloisForLFunctions.RHTower.GaussianTwoSquaresCount
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineInvariance
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Hecke's factorization of the Eisenstein series at `i`

Let `E(z, s) = ½ Σ_{gcd(c,d)=1} y^s/|cz + d|^{2s}` (`d4BMRawEisensteinPoincareSeries`) and let
`χ₋₄` be the odd character of conductor `4` (`chi4`).

* `latticeSum_eq` (Jacobi): `Σ_{(m,n) ≠ 0} (m² + n²)^{−s} = 4 ζ(s) L(s, χ₋₄)` for `Re s > 1`, from
  `#{z ∈ ℤ[i] : N(z) = n} = 4 Σ_{d ∣ n} χ₋₄(d)`.
* `latticeSum_eq_zeta_mul_primitive`: splitting off `gcd(m, n)`,
  `Σ_{(m,n) ≠ 0} (m² + n²)^{−s} = ζ(2s) Σ_{gcd(c,d)=1} (c² + d²)^{−s}`.
* `two_mul_zeta_mul_eisenstein_I` (Hecke): `2 ζ(2s) E(i, s) = 4 ζ(s) L(s, χ₋₄)` for `Re s > 1`.
* `eisensteinLineModel_I_eq` : the completed series `E*(i, s) = Λ(2s) E(i, s)` equals
  `2 Γ_ℝ(2s) ζ(s) L(s, χ₋₄)` for `Re s > 0`, `Im s > 0` (identity theorem): the zeros of `ζ` in the
  strip appear as zeros of the value `E*(i, s)`.
-/

open Complex LSeries
open RHTower.GaussianTwoSquares

local notation "ℤ[i]" => GaussianInt

namespace RHTower.HeckeFactorization

noncomputable section

/-- The odd character of conductor `4`. -/
def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chi4_apply (n : ℕ) : chi4 n = ((ZMod.χ₄ n : ℤ) : ℂ) := by
  simp [chi4, MulChar.ringHomComp_apply]

theorem chi4_ne_one : chi4 ≠ 1 := by
  intro h
  have h3 : chi4 ((3 : ℕ) : ZMod 4) = (1 : DirichletCharacter ℂ 4) ((3 : ℕ) : ZMod 4) := by rw [h]
  rw [chi4_apply, ZMod.χ₄_nat_three_mod_four (by norm_num), MulChar.one_apply (by decide)] at h3
  norm_num at h3

/-- `m² + n²` as a natural number. -/
def latNorm (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 + p.2 ^ 2).toNat

theorem latNorm_cast (p : ℤ × ℤ) : (latNorm p : ℤ) = p.1 ^ 2 + p.2 ^ 2 :=
  Int.toNat_of_nonneg (by positivity)

theorem latNorm_pos {p : ℤ × ℤ} (hp : p ≠ (0, 0)) : 0 < latNorm p := by
  have h : (0 : ℤ) < latNorm p := by
    rw [latNorm_cast]
    rcases eq_or_ne p.1 0 with h1 | h1
    · have h2 : p.2 ≠ 0 := fun h2 => hp (Prod.ext h1 h2)
      positivity
    · positivity
  exact_mod_cast h

/-- The lattice terms `(m² + n²)^{−s}` on nonzero pairs. -/
def latTerm (s : ℂ) (p : {p : ℤ × ℤ // p ≠ (0, 0)}) : ℂ := ((latNorm p.1 : ℕ) : ℂ) ^ (-s)

/-- The point `i` in coordinates. -/
def zI : D4BMUpperHalfPlaneCoordinate := ⟨0, 1, one_pos⟩

theorem quadratic_zI (p : ℤ × ℤ) : d4BMPoincareQuadratic zI p = (latNorm p : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (latNorm_cast p)
  simp only [Int.cast_natCast] at h
  rw [h, d4BMPoincareQuadratic, zI]
  push_cast
  ring

theorem summable_latTerm {s : ℂ} (hs : 1 < s.re) : Summable (latTerm s) := by
  refine Summable.of_norm_bounded (summable_d4BMPoincareQuadratic_cpow_norm zI ⟨s, hs⟩) fun p => ?_
  rw [latTerm, norm_natCast_cpow_of_pos (latNorm_pos p.2), quadratic_zI]
  simp

/-! ### Regrouping by the norm -/

/-- The fiber of `latNorm` over `n ≥ 1` is the set of Gaussian integers of norm `n`. -/
def fiberEquiv {n : ℕ} (hn : 0 < n) :
    ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}) ≃ ↥(normSet n) where
  toFun x := ⟨⟨x.1.1.1, x.1.1.2⟩, mem_normSet.mpr (by
    have h : latNorm x.1.1 = n := x.2
    rw [norm_eq]
    show x.1.1.1 ^ 2 + x.1.1.2 ^ 2 = n
    rw [← latNorm_cast, h])⟩
  invFun z := ⟨⟨(z.1.re, z.1.im), fun h => by
      have hz := mem_normSet.mp z.2
      rw [norm_eq] at hz
      have h1 : z.1.re = 0 := congrArg Prod.fst h
      have h2 : z.1.im = 0 := congrArg Prod.snd h
      rw [h1, h2] at hz
      have : (n : ℤ) = 0 := by rw [← hz]; ring
      omega⟩, by
    show latNorm (z.1.re, z.1.im) = n
    have hz := mem_normSet.mp z.2
    rw [norm_eq] at hz
    have : (latNorm (z.1.re, z.1.im) : ℤ) = n := by rw [latNorm_cast, hz]
    exact_mod_cast this⟩
  left_inv x := rfl
  right_inv z := rfl

theorem tsum_fiber {s : ℂ} (n : ℕ) :
    ∑' b : ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}), latTerm s b =
      LSeries.term (fun n => ((normSet n).card : ℂ)) s n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : IsEmpty ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {0}) :=
      ⟨fun x => (latNorm_pos x.1.2).ne' x.2⟩
    rw [tsum_empty, LSeries.term_zero]
  · have hconst : ∀ b : ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}),
        latTerm s b = (n : ℂ) ^ (-s) := fun b => by
      have h : latNorm b.1.1 = n := b.2
      rw [latTerm, h]
    simp_rw [hconst]
    rw [(fiberEquiv hn).tsum_eq (fun _ => (n : ℂ) ^ (-s)), Finset.tsum_subtype (normSet n)
      (fun _ => (n : ℂ) ^ (-s)), Finset.sum_const, LSeries.term_of_ne_zero hn.ne', nsmul_eq_mul,
      cpow_neg, div_eq_mul_inv]

/-- **Jacobi**: `Σ_{(m,n) ≠ 0} (m² + n²)^{−s} = 4 ζ(s) L(s, χ₋₄)`. -/
theorem latticeSum_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' p, latTerm s p = 4 * (riemannZeta s * DirichletCharacter.LFunction chi4 s) := by
  have hfib := (summable_latTerm hs).hasSum.tsum_fiberwise
    (fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1)
  simp_rw [tsum_fiber] at hfib
  have hL : LSeries (fun n => ((normSet n).card : ℂ)) s = ∑' p, latTerm s p := hfib.tsum_eq
  rw [← hL]
  have hconv : ∀ {n : ℕ}, n ≠ 0 → ((normSet n).card : ℂ) =
      ((4 : ℂ) • convolution 1 (fun n : ℕ => chi4 n)) n := by
    intro n hn
    have h := card_normSet (Nat.pos_of_ne_zero hn)
    have h' : ((normSet n).card : ℂ) = 4 * ((divisorChar n : ℤ) : ℂ) := by exact_mod_cast h
    rw [h', Pi.smul_apply, smul_eq_mul, LSeries.convolution_def]
    congr 1
    have hd := Nat.sum_divisorsAntidiagonal' (fun a b => (1 : ℕ → ℂ) a * chi4 b) (n := n)
    show _ = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * chi4 p.2
    rw [hd, divisorChar]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Pi.one_apply, one_mul, chi4_apply]
  rw [LSeries_congr hconv, LSeries_smul, LSeries_convolution'
    (LSeriesSummable_one_iff.mpr hs) (chi4.LSeriesSummable_of_one_lt_re hs),
    LSeries_one_eq_riemannZeta hs, DirichletCharacter.LFunction_eq_LSeries chi4 hs]

/-! ### Splitting off the gcd -/

theorem primExt {p q : D4BMPrimitiveIntegerPair} (h : p.pair = q.pair) : p = q := by
  cases p; cases q; simp_all

theorem gcd_pos_of_ne {p : ℤ × ℤ} (hp : p ≠ (0, 0)) : 0 < Int.gcd p.1 p.2 :=
  Int.gcd_pos_iff.mpr (by
    by_contra h
    push Not at h
    exact hp (Prod.ext h.1 h.2))

/-- `(k, (c, d)) ↦ ((k+1)c, (k+1)d)`. -/
def gcdEquiv : ℕ × D4BMPrimitiveIntegerPair ≃ {p : ℤ × ℤ // p ≠ (0, 0)} where
  toFun x := ⟨(((x.1 : ℤ) + 1) * x.2.pair.1, ((x.1 : ℤ) + 1) * x.2.pair.2), by
    intro h
    apply x.2.pair_ne_zero
    have hk : (x.1 : ℤ) + 1 ≠ 0 := by positivity
    have h1 : x.2.pair.1 = 0 := (mul_eq_zero.mp (congrArg Prod.fst h)).resolve_left hk
    have h2 : x.2.pair.2 = 0 := (mul_eq_zero.mp (congrArg Prod.snd h)).resolve_left hk
    exact Prod.ext h1 h2⟩
  invFun p := (Int.gcd p.1.1 p.1.2 - 1,
    ⟨(p.1.1 / Int.gcd p.1.1 p.1.2, p.1.2 / Int.gcd p.1.1 p.1.2),
      Int.gcd_div_gcd_div_gcd (gcd_pos_of_ne p.2)⟩)
  left_inv x := by
    obtain ⟨k, q⟩ := x
    have hk : (k : ℤ) + 1 ≠ 0 := by positivity
    have hc : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have hg : Int.gcd (((k : ℤ) + 1) * q.pair.1) (((k : ℤ) + 1) * q.pair.2) = k + 1 := by
      rw [Int.gcd_mul_left, q.primitive, hc, Int.natAbs_natCast, mul_one]
    have hg' : ((Int.gcd (((k : ℤ) + 1) * q.pair.1) (((k : ℤ) + 1) * q.pair.2) : ℕ) : ℤ) =
        (k : ℤ) + 1 := by rw [hg, hc]
    refine Prod.ext ?_ (primExt ?_)
    · show Int.gcd (((k : ℤ) + 1) * q.pair.1) (((k : ℤ) + 1) * q.pair.2) - 1 = k
      rw [hg]; rfl
    · show ((((k : ℤ) + 1) * q.pair.1) / (Int.gcd (((k : ℤ) + 1) * q.pair.1)
          (((k : ℤ) + 1) * q.pair.2) : ℤ), (((k : ℤ) + 1) * q.pair.2) /
          (Int.gcd (((k : ℤ) + 1) * q.pair.1) (((k : ℤ) + 1) * q.pair.2) : ℤ)) = q.pair
      rw [hg', Int.mul_ediv_cancel_left _ hk, Int.mul_ediv_cancel_left _ hk]
  right_inv p := by
    obtain ⟨⟨m, n⟩, hp⟩ := p
    have hg0 : 0 < Int.gcd m n := gcd_pos_of_ne hp
    have hsub : (((Int.gcd m n - 1 : ℕ) : ℤ) + 1) = (Int.gcd m n : ℤ) := by omega
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (((Int.gcd m n - 1 : ℕ) : ℤ) + 1) * (m / Int.gcd m n) = m
      rw [hsub]
      exact Int.mul_ediv_cancel' (Int.gcd_dvd_left m n)
    · show (((Int.gcd m n - 1 : ℕ) : ℤ) + 1) * (n / Int.gcd m n) = n
      rw [hsub]
      exact Int.mul_ediv_cancel' (Int.gcd_dvd_right m n)

theorem latNorm_gcdEquiv (k : ℕ) (q : D4BMPrimitiveIntegerPair) :
    latNorm (gcdEquiv (k, q)).1 = (k + 1) ^ 2 * latNorm q.pair := by
  have h : (latNorm (gcdEquiv (k, q)).1 : ℤ) = ((k + 1) ^ 2 * latNorm q.pair : ℕ) := by
    rw [latNorm_cast]
    push_cast
    rw [latNorm_cast]
    show (((k : ℤ) + 1) * q.pair.1) ^ 2 + (((k : ℤ) + 1) * q.pair.2) ^ 2 = _
    ring
  exact_mod_cast h

theorem natCast_sq_cpow_neg (k : ℕ) (s : ℂ) :
    (((k + 1) ^ 2 : ℕ) : ℂ) ^ (-s) = 1 / ((k : ℂ) + 1) ^ (2 * s) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have e : (((k + 1) ^ 2 : ℕ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) ^ (2 : ℂ) := by
    rw [cpow_two]; push_cast; ring
  rw [e, ← cpow_mul _ (by rw [← ofReal_log hpos.le]; norm_num [Real.pi_pos])
    (by rw [← ofReal_log hpos.le]; norm_num [Real.pi_pos.le])]
  rw [show (2 : ℂ) * -s = -(2 * s) by ring, cpow_neg, one_div]
  push_cast
  rfl

/-- **Splitting off the gcd**: `Σ_{(m,n) ≠ 0} (m² + n²)^{−s} = ζ(2s) Σ_{gcd(c,d)=1} (c² + d²)^{−s}`. -/
theorem latticeSum_eq_zeta_mul_primitive {s : ℂ} (hs : 1 < s.re) :
    ∑' p, latTerm s p = riemannZeta (2 * s) *
      ∑' q : D4BMPrimitiveIntegerPair, ((latNorm q.pair : ℕ) : ℂ) ^ (-s) := by
  have hsum := (summable_latTerm hs)
  have hsum' : Summable (latTerm s ∘ gcdEquiv) := (gcdEquiv.summable_iff).mpr hsum
  have hpt : ∀ x : ℕ × D4BMPrimitiveIntegerPair, (latTerm s ∘ gcdEquiv) x =
      (1 / ((x.1 : ℂ) + 1) ^ (2 * s)) * ((latNorm x.2.pair : ℕ) : ℂ) ^ (-s) := fun x => by
    obtain ⟨k, q⟩ := x
    simp only [Function.comp_apply, latTerm, latNorm_gcdEquiv]
    rw [Nat.cast_mul, natCast_mul_natCast_cpow, natCast_sq_cpow_neg]
  calc ∑' p, latTerm s p = ∑' x, (latTerm s ∘ gcdEquiv) x := (gcdEquiv.tsum_eq (latTerm s)).symm
    _ = ∑' k, ∑' q, (latTerm s ∘ gcdEquiv) (k, q) := hsum'.tsum_prod
    _ = _ := by
      simp_rw [hpt, tsum_mul_left]
      rw [tsum_mul_right, ← zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith)]

/-! ### Hecke's factorization -/

theorem seed_zI (s : ℂ) (q : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed zI s q = ((latNorm q.pair : ℕ) : ℂ) ^ (-s) := by
  have hpos : (0 : ℝ) < latNorm q.pair := by exact_mod_cast latNorm_pos q.pair_ne_zero
  rw [d4BMPoincareSeed, quadratic_zI, show zI.y = 1 from rfl, one_div, ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hpos.le]; exact Real.pi_ne_zero.symm), ← cpow_neg]
  rfl

/-- **Hecke's factorization at `i`**: `2 ζ(2s) E(i, s) = 4 ζ(s) L(s, χ₋₄)` for `Re s > 1`. -/
theorem two_mul_zeta_mul_eisenstein_I {s : ℂ} (hs : 1 < s.re) :
    2 * riemannZeta (2 * s) * d4BMRawEisensteinPoincareSeries zI ⟨s, hs⟩ =
      4 * riemannZeta s * DirichletCharacter.LFunction chi4 s := by
  rw [d4BMRawEisensteinPoincareSeries]
  simp_rw [seed_zI]
  have h := (latticeSum_eq_zeta_mul_primitive hs).symm.trans (latticeSum_eq hs)
  calc 2 * riemannZeta (2 * s) * (1 / 2 * ∑' q : D4BMPrimitiveIntegerPair,
        ((latNorm q.pair : ℕ) : ℂ) ^ (-s))
      = riemannZeta (2 * s) * ∑' q : D4BMPrimitiveIntegerPair, ((latNorm q.pair : ℕ) : ℂ) ^ (-s) := by
        ring
    _ = 4 * riemannZeta s * DirichletCharacter.LFunction chi4 s := by rw [h]; ring

/-! ### The completed series at `i` on the strip -/

theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hG : Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) := funext Gammaℝ_def
  rw [hG]
  refine DifferentiableAt.mul ?_ ?_
  · exact ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl (by
      exact_mod_cast Real.pi_ne_zero))
  · refine (differentiableAt_Gamma _ fun m h => ?_).comp s (differentiableAt_id.div_const 2)
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith

/-- **`E*(i, s) = 2 Γ_ℝ(2s) ζ(s) L(s, χ₋₄)` for `Re s > 1`.** -/
theorem eisensteinLineModel_I_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    eisensteinLineModel (s - 1 / 2) UpperHalfPlane.I =
      2 * Gammaℝ (2 * s) * riemannZeta s * DirichletCharacter.LFunction chi4 s := by
  have h := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg zI ⟨s, hs⟩ 0
  have hI : eisensteinLineModel (s - 1 / 2) UpperHalfPlane.I =
      d4BMCompletedEisensteinCuspLeg .scalar (s - 1 / 2) 0 zI.y := by
    rw [eisensteinLineModel, UpperHalfPlane.I_re, UpperHalfPlane.I_im]
    rfl
  rw [hI, ← h]
  show reflectedCompletedLambda (2 * s) * d4BMRawEisensteinPoincareSeries zI ⟨s, hs⟩ = _
  have hH := two_mul_zeta_mul_eisenstein_I hs
  rw [reflectedCompletedLambda]
  linear_combination Gammaℝ (2 * s) / 2 * hH

/-- **Hecke's factorization of `E*(i, s)` on the strip.**  For `Re s > 0` and `Im s > 0`,
`E*(i, s) = 2 Γ_ℝ(2s) ζ(s) L(s, χ₋₄)`. -/
theorem eisensteinLineModel_I_eq {s : ℂ} (hs : 0 < s.re) (him : 0 < s.im) :
    eisensteinLineModel (s - 1 / 2) UpperHalfPlane.I =
      2 * Gammaℝ (2 * s) * riemannZeta s * DirichletCharacter.LFunction chi4 s := by
  set F : ℂ → ℂ := fun u => eisensteinLineModel u UpperHalfPlane.I
  set G : ℂ → ℂ := fun u => 2 * Gammaℝ (2 * (u + 1 / 2)) * riemannZeta (u + 1 / 2) *
    DirichletCharacter.LFunction chi4 (u + 1 / 2)
  have hF : DifferentiableOn ℂ F eisensteinLineDomain := by
    have h := differentiableOn_cuspLeg 0 (Y := 1) one_pos
    refine h.congr fun u _ => ?_
    simp only [F, eisensteinLineModel, UpperHalfPlane.I_re, UpperHalfPlane.I_im]
  have hG : DifferentiableOn ℂ G eisensteinLineDomain := by
    intro u hu
    have hre : 0 < (2 * (u + 1 / 2)).re := by simp; linarith [hu.1]
    have hne : u + 1 / 2 ≠ 1 := fun h => by
      have := congrArg Complex.im h
      simp at this
      exact hu.2.ne' this
    refine DifferentiableAt.differentiableWithinAt ?_
    refine ((DifferentiableAt.const_mul ?_ 2).mul ?_).mul ?_
    · exact (differentiableAt_Gammaℝ_of_re_pos hre).comp u
        ((differentiableAt_id.add_const _).const_mul (2 : ℂ))
    · exact (differentiableAt_riemannZeta hne).comp u (differentiableAt_id.add_const _)
    · exact (DirichletCharacter.differentiable_LFunction chi4_ne_one _).comp u
        (differentiableAt_id.add_const _)
  have hEq : Set.EqOn F G eisensteinLineDomain := by
    refine (hF.analyticOnNhd isOpen_eisensteinLineDomain).eqOn_of_preconnected_of_eventuallyEq
      (hG.analyticOnNhd isOpen_eisensteinLineDomain) isPreconnected_eisensteinLineDomain
      (z₀ := 1 + Complex.I) ⟨by simp; norm_num, by simp⟩ ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 2 : ℝ) < (1 + Complex.I).re by simp; norm_num)] with u hu
    have h := eisensteinLineModel_I_eq_of_one_lt (s := u + 1 / 2) (by
      have hu' : (1 / 2 : ℝ) < u.re := hu
      simp; linarith)
    simp only [F, G]
    rw [← h]
    ring_nf
  have hmem : s - 1 / 2 ∈ eisensteinLineDomain := ⟨by simp; linarith, by simpa using him⟩
  have h := hEq hmem
  simp only [F, G, sub_add_cancel] at h
  exact h

/-- **The zeros of `ζ` in the strip are zeros of the value `E*(i, s)`.** -/
theorem eisensteinLineModel_I_eq_zero_iff {s : ℂ} (hs : 0 < s.re) (him : 0 < s.im) :
    eisensteinLineModel (s - 1 / 2) UpperHalfPlane.I = 0 ↔
      riemannZeta s = 0 ∨ DirichletCharacter.LFunction chi4 s = 0 := by
  rw [eisensteinLineModel_I_eq hs him]
  have hΓ : Gammaℝ (2 * s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (mul_ne_zero two_ne_zero hΓ)
      · exact Or.inl h2
    · exact Or.inr h1
  · rintro (h | h) <;> simp [h]

/-- **In the `2s`-variable the zeros are one-sided**: if `Λ(2s) = 0` with `Im s ≠ 0`, then
`0 < Re s < ½`. -/
theorem re_lt_half_of_lambda_two_mul_eq_zero {s : ℂ} (h : reflectedCompletedLambda (2 * s) = 0)
    (him : s.im ≠ 0) : 0 < s.re ∧ s.re < 1 / 2 := by
  have hne : ∀ w : ℂ, 1 ≤ w.re → reflectedCompletedLambda w ≠ 0 := fun w hw => by
    rw [reflectedCompletedLambda]
    exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by linarith))
      (riemannZeta_ne_zero_of_one_le_re hw)
  have hw : (2 * s).im ≠ 0 := by simp [him]
  constructor
  · by_contra hle
    push Not at hle
    have hfe := reflectedCompletedLambda_one_sub_of_im hw
    have h1 : 1 ≤ (1 - 2 * s).re := by simp; linarith
    exact hne _ h1 (by rw [hfe]; exact h)
  · by_contra hle
    push Not at hle
    exact hne _ (by simp; linarith) h

end

end RHTower.HeckeFactorization
