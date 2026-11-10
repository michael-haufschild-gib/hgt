import GaloisForLFunctions.HyperbolicArakelovTheory.ThePrimeAdjacencyOnTheAdelicCarrier
import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePlacesAreTrees
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Leaf and Hecke separation on the projective adelic carrier

On `X = Γ \ (ℍ³ × Π'_p PGL₂(ℚ_p)/K_p)`, `Γ = J⁻¹ SL₂(ℚ) J`, the archimedean Laplacian acts
along the `ℍ³`-leaves (preserving `Γ`-orbits in `FiniteVertices`) while the prime adjacency
operators `A_p` act along the finite fibres (preserving `SL₂(ℚ)`-orbits in `ℍ³`). Neither
foliation alone, nor any bounded-rank combination of prime operators with `ℍ³`-kernels, can
couple all pairs of degree points `[x_m], [x_n]`:

1. **Finite-leaf parity classification (`same_finite_leaf_iff_isSquare`).** Each local building
   `PGL₂(ℚ_p)/K_p` carries a `PGL₂(ℚ_p)`-covariant determinant-valuation parity `EvenVertex p`,
   preserved by `Γ` and flipped by `A_p`. Two degree points `x_m, x_n` lie in the same finite
   `Γ`-orbit if and only if `m * n` is a square.
2. **Unbounded place-rank obstruction (`primeWord_eq_zero_of_odd_outside`,
   `primeWord_eq_zero_and_weilDeltaKernel_pos`).** A product of `r` prime operators flips parity
   at at most `r` primes, so every operator coupling arbitrary `ℍ³`-kernels with products of at
   most `r` prime operators vanishes between `[x_1]` and `[x_n]` whenever `n` is a product of
   `r + 1 ≥ 2` distinct primes, where `weilDeltaKernel 1 n > 0`.
3. **Archimedean-leaf sum-of-two-squares classification (`same_arch_orbit_iff_sum_two_squares`)
   and Hecke disjointness (`primeOperator_indicator_degree_eq_zero`,
   `primeWord_indicator_degree_eq_zero_of_mod_four`).** Two degree points `x_m, x_n` have `ℍ³`
   coordinates in the same `SL₂(ℚ)`-orbit if and only if `m * n = a² + b²` in `ℕ`. Hence the
   entire Hecke algebra `ℝ[{A_q}_q]` vanishes between `[x_1]` and `[x_p]` for every prime
   `p ≡ 3 (mod 4)`; moreover, a single step `A_p` vanishes between `[x_1]` and `[x_p]` for
   *every* prime `p` (`1 / p = z₀² + z₁²` has no integer solution).
-/

set_option autoImplicit false
noncomputable section

open Matrix Set Finset
open scoped Classical ComplexConjugate

namespace GaloisForLFunctions.HyperbolicArakelovTheory.CarrierSeparation

open FullAdelic AdelicAdjacency SurfaceOfSpecZ

local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

/-! ## 1. Local determinant-valuation parity on `PGL₂(ℚ_p)/K_p` -/

/-- A nonzero `p`-adic scalar has even valuation when its norm is an even integer power of `p`. -/
def EvenPadicNorm (p : {p : ℕ // p.Prime}) (x : ℚ_[p.1]) : Prop :=
  ∃ k : ℤ, ‖x‖ = (p.1 : ℝ) ^ (2 * k)

private theorem prime_real_pos (p : {p : ℕ // p.Prime}) : (0 : ℝ) < p.1 := by
  exact_mod_cast p.2.pos

private theorem prime_real_ne_one (p : {p : ℕ // p.Prime}) : (p.1 : ℝ) ≠ 1 := by
  exact_mod_cast p.2.ne_one

private theorem norm_eq_prime_zpow (p : {p : ℕ // p.Prime}) {x : ℚ_[p.1]} (hx : x ≠ 0) :
    ∃ a : ℤ, ‖x‖ = (p.1 : ℝ) ^ a := by
  obtain ⟨n, hn⟩ := Padic.padicNormE.image hx
  refine ⟨-n, ?_⟩
  rw [hn]
  push_cast
  rfl

private theorem evenPadicNorm_iff_of_zpow (p : {p : ℕ // p.Prime}) {x : ℚ_[p.1]} {a : ℤ}
    (hx : ‖x‖ = (p.1 : ℝ) ^ a) : EvenPadicNorm p x ↔ ∃ k : ℤ, a = 2 * k := by
  unfold EvenPadicNorm
  rw [hx]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (zpow_right_inj₀ (prime_real_pos p) (prime_real_ne_one p)).mp hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

theorem evenPadicNorm_one (p : {p : ℕ // p.Prime}) : EvenPadicNorm p 1 :=
  ⟨0, by simp⟩

theorem not_evenPadicNorm_prime (p : {p : ℕ // p.Prime}) : ¬ EvenPadicNorm p (p.1 : ℚ_[p.1]) := by
  have hp : ‖(p.1 : ℚ_[p.1])‖ = (p.1 : ℝ) ^ (-1 : ℤ) := by
    rw [Padic.norm_p, _root_.zpow_neg_one]
  rw [evenPadicNorm_iff_of_zpow p hp]
  rintro ⟨k, hk⟩
  omega

theorem evenPadicNorm_mul_iff (p : {p : ℕ // p.Prime}) {x y : ℚ_[p.1]} (hx : x ≠ 0) (hy : y ≠ 0) :
    EvenPadicNorm p (x * y) ↔ (EvenPadicNorm p x ↔ EvenPadicNorm p y) := by
  obtain ⟨a, ha⟩ := norm_eq_prime_zpow p hx
  obtain ⟨b, hb⟩ := norm_eq_prime_zpow p hy
  have hxy : ‖x * y‖ = (p.1 : ℝ) ^ (a + b) := by
    rw [norm_mul, ha, hb, ← zpow_add₀ (prime_real_pos p).ne']
  rw [evenPadicNorm_iff_of_zpow p hxy, evenPadicNorm_iff_of_zpow p ha,
    evenPadicNorm_iff_of_zpow p hb]
  constructor
  · rintro ⟨k, hk⟩
    constructor
    · rintro ⟨ka, rfl⟩; exact ⟨k - ka, by omega⟩
    · rintro ⟨kb, rfl⟩; exact ⟨k - kb, by omega⟩
  · intro h
    by_cases he : ∃ k : ℤ, a = 2 * k
    · obtain ⟨ka, rfl⟩ := he
      obtain ⟨kb, rfl⟩ := h.mp ⟨ka, rfl⟩
      exact ⟨ka + kb, by omega⟩
    · have hnb : ¬ ∃ k : ℤ, b = 2 * k := fun hb' => he (h.mpr hb')
      have ha_ne : a ≠ 2 * (a / 2) := fun h0 => he ⟨a / 2, h0⟩
      have hb_ne : b ≠ 2 * (b / 2) := fun h0 => hnb ⟨b / 2, h0⟩
      have ha_odd : a = 2 * (a / 2) + 1 := by omega
      have hb_odd : b = 2 * (b / 2) + 1 := by omega
      exact ⟨a / 2 + b / 2 + 1, by omega⟩

theorem evenPadicNorm_inv_iff (p : {p : ℕ // p.Prime}) {x : ℚ_[p.1]} (hx : x ≠ 0) :
    EvenPadicNorm p x⁻¹ ↔ EvenPadicNorm p x := by
  have h := evenPadicNorm_mul_iff p hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx] at h
  have h1 := evenPadicNorm_one p
  tauto

theorem evenPadicNorm_sq (p : {p : ℕ // p.Prime}) {u : ℚ_[p.1]} (hu : u ≠ 0) :
    EvenPadicNorm p (u ^ 2) := by
  rw [sq, evenPadicNorm_mul_iff p hu hu]

theorem evenPadicNorm_natCast_iff (p : {p : ℕ // p.Prime}) (n : ℕ+) :
    EvenPadicNorm p ((n : ℕ) : ℚ_[p.1]) ↔ Even ((n : ℕ).factorization p.1) := by
  set k := (n : ℕ).factorization p.1
  set m := (n : ℕ) / p.1 ^ k
  have hdvd : p.1 ^ k ∣ (n : ℕ) := Nat.ordProj_dvd (n : ℕ) p.1
  have hndvd : ¬ p.1 ∣ m := Nat.not_dvd_ordCompl p.2 n.ne_zero
  have hnm : (n : ℕ) = p.1 ^ k * m := (Nat.mul_div_cancel' hdvd).symm
  have hm_norm : ‖(m : ℚ_[p.1])‖ = 1 := by
    change ‖((m : ℚ) : ℚ_[p.1])‖ = 1
    rw [Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff (p := p.1) m).mpr hndvd]
    exact Rat.cast_one
  have hn_norm : ‖((n : ℕ) : ℚ_[p.1])‖ = (p.1 : ℝ) ^ (-(k : ℤ)) := by
    conv_lhs => rw [hnm]
    push_cast
    rw [norm_mul, Padic.norm_p_pow, hm_norm, mul_one]
  rw [evenPadicNorm_iff_of_zpow p hn_norm, even_iff_exists_two_mul]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(-z).toNat, ?_⟩
    omega
  · rintro ⟨j, hj⟩
    exact ⟨-(j : ℤ), by omega⟩

/-- Determinant-valuation parity descends to `PGL₂(ℚ_p)` since scalar matrices have square determinants. -/
def EvenPGL (p : {p : ℕ // p.Prime}) : LocalPGL p → Prop :=
  Quotient.lift (fun g : LocalGL p => EvenPadicNorm p g.val.det) (by
    intro g₁ g₂ h
    have hmk : ProjGenLinGroup.mk g₁ = ProjGenLinGroup.mk g₂ := Quotient.sound h
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmk
    have hdet : g₂.val.det = g₁.val.det * (u.val ^ 2) := by
      rw [← hu, GeneralLinearGroup.coe_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar,
        Matrix.det_fin_two]
      simp [Matrix.scalar_apply, sq]
    apply propext
    rw [hdet, evenPadicNorm_mul_iff p g₁.det_ne_zero (pow_ne_zero 2 u.ne_zero)]
    have hsq := evenPadicNorm_sq p u.ne_zero
    tauto)

@[simp] theorem evenPGL_mk (p : {p : ℕ // p.Prime}) (g : LocalGL p) :
    EvenPGL p (ProjGenLinGroup.mk g) ↔ EvenPadicNorm p g.val.det := Iff.rfl

theorem evenPGL_one (p : {p : ℕ // p.Prime}) : EvenPGL p 1 := by
  change EvenPadicNorm p (1 : LocalGL p).val.det
  simp [evenPadicNorm_one]

theorem evenPGL_mul (p : {p : ℕ // p.Prime}) (x y : LocalPGL p) :
    EvenPGL p (x * y) ↔ (EvenPGL p x ↔ EvenPGL p y) := by
  induction x using Quotient.inductionOn with
  | h g₁ =>
    induction y using Quotient.inductionOn with
    | h g₂ =>
      change EvenPadicNorm p (g₁ * g₂).val.det ↔ _
      rw [GeneralLinearGroup.coe_mul, Matrix.det_mul]
      exact evenPadicNorm_mul_iff p g₁.det_ne_zero g₂.det_ne_zero

theorem evenPGL_inv (p : {p : ℕ // p.Prime}) (x : LocalPGL p) :
    EvenPGL p x⁻¹ ↔ EvenPGL p x := by
  have h := evenPGL_mul p x x⁻¹
  rw [mul_inv_cancel] at h
  have h1 := evenPGL_one p
  tauto

theorem evenPGL_of_mem_integralPGL (p : {p : ℕ // p.Prime}) {x : LocalPGL p}
    (hx : x ∈ integralPGL p) : EvenPGL p x := by
  obtain ⟨h, rfl⟩ := hx
  change EvenPadicNorm p (integralMap p h).val.det
  exact ⟨0, by rw [integralMap_det_norm]; simp⟩

/-- Determinant-valuation parity on the local Bruhat–Tits vertex set `PGL₂(ℚ_p)/K_p`. -/
def EvenVertex (p : {p : ℕ // p.Prime}) : LocalVertex p → Prop :=
  Quotient.lift (EvenPGL p) (by
    intro x y h
    have hmem : x⁻¹ * y ∈ integralPGL p := QuotientGroup.leftRel_apply.mp h
    have he := evenPGL_of_mem_integralPGL p hmem
    have hmul : y = x * (x⁻¹ * y) := by group
    apply propext
    conv_rhs => rw [hmul, evenPGL_mul]
    tauto)

theorem evenVertex_smul (p : {p : ℕ // p.Prime}) (g : LocalPGL p) (v : LocalVertex p) :
    EvenVertex p (g • v) ↔ (EvenPGL p g ↔ EvenVertex p v) := by
  induction v using Quotient.inductionOn with
  | h x => exact evenPGL_mul p g x

theorem evenVertex_base (p : {p : ℕ // p.Prime}) : EvenVertex p (baseVertex p) :=
  evenPGL_one p

theorem not_evenVertex_neighbor_none (p : {p : ℕ // p.Prime}) :
    ¬ EvenVertex p (neighbor p none) := by
  change ¬ EvenPadicNorm p (neighborRep p none).val.det
  rw [neighborRep_det]
  exact not_evenPadicNorm_prime p

/-- Every tree adjacency edge flips determinant parity. -/
theorem evenVertex_of_adjacent (p : {p : ℕ // p.Prime}) {v w : LocalVertex p}
    (h : Adjacent p v w) : EvenVertex p w ↔ ¬ EvenVertex p v := by
  obtain ⟨g, rfl, rfl⟩ := h
  rw [evenVertex_smul, evenVertex_smul]
  have hb := evenVertex_base p
  have hn := not_evenVertex_neighbor_none p
  tauto

theorem evenPGL_localProj (p : {p : ℕ // p.Prime}) (g : OppositeAdelic.RationalGroup) :
    EvenPGL p (localProj p g) := by
  rw [localProj_toGL, evenPGL_mk]
  have hdet : (localGLMap p (SpecialLinearGroup.toGL g)).val.det = 1 := by
    have hg := g.prop
    rw [Matrix.det_fin_two] at hg ⊢
    change ((g 0 0 : ℚ) : ℚ_[p.1]) * ((g 1 1 : ℚ) : ℚ_[p.1]) -
      ((g 0 1 : ℚ) : ℚ_[p.1]) * ((g 1 0 : ℚ) : ℚ_[p.1]) = 1
    exact_mod_cast hg
  rw [hdet]
  exact evenPadicNorm_one p

/-- The Weyl-conjugated rational group preserves local vertex parity at every prime. -/
theorem evenVertex_conjugate_smul (p : {p : ℕ // p.Prime})
    (g : OppositeAdelic.RationalGroup) (x : GlobalSpace) :
    EvenVertex p ((conjugateEmbedding g • x).2.1 p) ↔ EvenVertex p (x.2.1 p) := by
  rw [conjugate_arithmetic_smul]
  change EvenVertex p (localProj p (OppositeAdelic.weyl⁻¹ * g * OppositeAdelic.weyl) • x.2.1 p) ↔ _
  rw [evenVertex_smul]
  have he := evenPGL_localProj p (OppositeAdelic.weyl⁻¹ * g * OppositeAdelic.weyl)
  tauto

/-- At degree `n`, vertex parity at `p` is the parity of `v_p(n)`. -/
theorem evenVertex_originalDegreePoint (p : {p : ℕ // p.Prime}) (n : ℕ+) :
    EvenVertex p ((originalDegreePoint n).2.1 p) ↔ Even ((n : ℕ).factorization p.1) := by
  change EvenPadicNorm p (localGLMap p (upperDegree n)).val.det ↔ _
  have hdet : (localGLMap p (upperDegree n)).val.det = ((n : ℕ) : ℚ_[p.1]) := by
    rw [Matrix.det_fin_two]
    simp [localGLMap_apply, upperDegree]
  rw [hdet]
  exact evenPadicNorm_natCast_iff p n

/-! ## 2. Exact classification of finite leaves and unbounded place-rank obstruction -/

/-- Two degree points lie on the same finite `Γ`-orbit (the same `ℍ³`-leaf of `X`) if and only if
their product `m * n` is a square. -/
theorem same_finite_leaf_iff_isSquare (m n : ℕ+) :
    (∃ γ : conjugateArithmeticGroup,
      (γ • originalDegreePoint n).2 = (originalDegreePoint m).2) ↔
    IsSquare ((m : ℕ) * n) := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, hg⟩ := γ.property
    have hf : (conjugateEmbedding g • originalDegreePoint n).2 = (originalDegreePoint m).2 := by
      change ((γ : AdelicGroup) • originalDegreePoint n).2 = _ at hγ
      rwa [← hg] at hγ
    have hev : ∀ q : ℕ, q.Prime → Even (((m : ℕ) * n).factorization q) := by
      intro q hq
      let p : {p : ℕ // p.Prime} := ⟨q, hq⟩
      have hp := congrArg (fun v : FiniteVertices => EvenVertex p (v.1 p)) hf
      rw [evenVertex_conjugate_smul, evenVertex_originalDegreePoint,
        evenVertex_originalDegreePoint] at hp
      rw [Nat.factorization_mul m.ne_zero n.ne_zero, Finsupp.add_apply, Nat.even_add]
      exact Eq.to_iff hp.symm
    have hprod : ∏ p ∈ ((m : ℕ) * n).primeFactors,
        p ^ (2 * (((m : ℕ) * n).factorization p / 2)) = (m : ℕ) * n := by
      conv_rhs => rw [Nat.prod_primeFactors_pow_factorization (mul_ne_zero m.ne_zero n.ne_zero)]
      refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp (hev p (Nat.prime_of_mem_primeFactors hp))
      rw [hk, Nat.mul_div_cancel_left _ two_pos]
    refine ⟨∏ p ∈ ((m : ℕ) * n).primeFactors, p ^ (((m : ℕ) * n).factorization p / 2), ?_⟩
    rw [← sq, ← Finset.prod_pow]
    simp_rw [← pow_mul, mul_comm _ 2]
    exact hprod.symm
  · rintro ⟨k, hk⟩
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hk
      exact (mul_ne_zero m.ne_zero n.ne_zero) hk
    let q : ℚ := (k : ℚ) / (m : ℕ)
    have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast hk0) (by exact_mod_cast m.ne_zero)
    have hq_sq : q ^ 2 = ((n : ℕ) : ℚ) / (m : ℕ) := by
      have hkQ : ((m : ℕ) : ℚ) * (n : ℕ) = (k : ℚ) ^ 2 := by exact_mod_cast hk.trans (sq k).symm
      dsimp only [q]
      field_simp [show ((m : ℕ) : ℚ) ≠ 0 by exact_mod_cast m.ne_zero]
      linarith
    let g := OppositeAdelic.diagonal q hq
    refine ⟨⟨conjugateEmbedding g, ⟨g, rfl⟩⟩, ?_⟩
    change (conjugateEmbedding g • originalDegreePoint n).2 = finitePoint (upperDegree m)
    rw [conjugate_arithmetic_smul]
    change (OppositeAdelic.weyl⁻¹ * g * OppositeAdelic.weyl) • finitePoint (upperDegree n) =
      finitePoint (upperDegree m)
    have hw : OppositeAdelic.weyl⁻¹ * g * OppositeAdelic.weyl =
        OppositeAdelic.diagonal q⁻¹ (inv_ne_zero hq) := by
      dsimp only [g]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [OppositeAdelic.weyl, OppositeAdelic.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hw, finite_smul_point]
    have hGL : upperDegree m * GeneralLinearGroup.scalar (Fin 2) (Units.mk0 q hq) =
        SpecialLinearGroup.toGL (OppositeAdelic.diagonal q⁻¹ (inv_ne_zero hq)) * upperDegree n := by
      have hqn : ((m : ℕ) : ℚ) * q = q⁻¹ * (n : ℕ) := by
        have h1 : ((m : ℕ) : ℚ) * q ^ 2 = (n : ℕ) := by
          rw [hq_sq, mul_div_cancel₀ _ (by exact_mod_cast m.ne_zero)]
        calc ((m : ℕ) : ℚ) * q = q⁻¹ * (((m : ℕ) : ℚ) * q ^ 2) := by field_simp [hq]
          _ = q⁻¹ * (n : ℕ) := by rw [h1]
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upperDegree, GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, OppositeAdelic.diagonal, SpecialLinearGroup.toGL,
          Matrix.mul_apply, Fin.sum_univ_two]
      exact hqn
    apply Subtype.ext
    funext p
    apply congrArg QuotientGroup.mk
    symm
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨Units.mk0 (q : ℚ_[p.1]) (by exact_mod_cast hq), ?_⟩
    have hloc := congrArg (localGLMap p) hGL
    rw [map_mul] at hloc
    refine Eq.trans ?_ hloc
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [localGLMap_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- Parity at a prime `p` descends to `ConjugateCarrier = Γ \ GlobalSpace`. -/
def EvenClass (p : {p : ℕ // p.Prime}) : ConjugateCarrier → Prop :=
  Quotient.lift (fun x : GlobalSpace => EvenVertex p (x.2.1 p)) (by
    intro x y h
    obtain ⟨γ, hγ⟩ := h
    obtain ⟨g, hg⟩ := γ.property
    have he : conjugateEmbedding g • y = x := by
      change (γ : AdelicGroup) • y = x at hγ
      rwa [← hg] at hγ
    rw [← he]
    exact propext (evenVertex_conjugate_smul p g y))

@[simp] theorem evenClass_carrierClass (p : {p : ℕ // p.Prime}) (x : GlobalSpace) :
    EvenClass p (carrierClass x) ↔ EvenVertex p (x.2.1 p) := Iff.rfl

theorem evenClass_originalDegreeClass (p : {p : ℕ // p.Prime}) (n : ℕ+) :
    EvenClass p (originalDegreeClass n) ↔ Even ((n : ℕ).factorization p.1) :=
  evenVertex_originalDegreePoint p n

/-- Iterated prime adjacency along a word `L` of primes. -/
def primeWord (L : List {p : ℕ // p.Prime}) (F : ConjugateCarrier → ℝ) :
    ConjugateCarrier → ℝ :=
  L.foldr primeOperator F

/-- If `F` vanishes outside classes having parity `b` at a prime `q ∉ L`, then `primeWord L F`
also vanishes outside classes having parity `b` at `q`. -/
theorem primeWord_eq_zero_of_outside (L : List {p : ℕ // p.Prime}) (q : {p : ℕ // p.Prime})
    (hq : q ∉ L) (b : Prop) (F : ConjugateCarrier → ℝ)
    (hF : ∀ c, (EvenClass q c ↔ b) → F c = 0) :
    ∀ c, (EvenClass q c ↔ b) → primeWord L F c = 0 := by
  induction L with
  | nil => exact hF
  | cons p L ih =>
    have hpq : q ≠ p := fun e => hq (List.mem_cons.mpr (Or.inl e))
    have hqL : q ∉ L := fun hm => hq (List.mem_cons.mpr (Or.inr hm))
    intro c hc
    induction c using Quotient.inductionOn with
    | h x =>
      change primeOperator p (primeWord L F) (carrierClass x) = 0
      rw [primeOperator_apply]
      refine Finset.sum_eq_zero fun w _ => ih hqL _ ?_
      rw [evenClass_carrierClass]
      change EvenVertex q ((replaceVertex p x.2 w).1 q) ↔ b
      rw [replaceVertex_away p x.2 w q hpq]
      exact hc

/-- Any prime-operator word `L` missing an odd-exponent prime of `m * n` annihilates the
coupling between `[x_m]` and `[x_n]`. -/
theorem primeWord_eq_zero_of_odd_outside (L : List {p : ℕ // p.Prime}) {m n : ℕ+}
    (q : {p : ℕ // p.Prime}) (hq : q ∉ L)
    (hodd : ¬ Even (((m : ℕ) * n).factorization q.1))
    (F : ConjugateCarrier → ℝ) (hF : ∀ c, c ≠ originalDegreeClass n → F c = 0) :
    primeWord L F (originalDegreeClass m) = 0 := by
  have hdiff : ¬ (Even ((m : ℕ).factorization q.1) ↔ Even ((n : ℕ).factorization q.1)) := by
    intro hiff
    apply hodd
    rw [Nat.factorization_mul m.ne_zero n.ne_zero, Finsupp.add_apply, Nat.even_add]
    exact hiff
  refine primeWord_eq_zero_of_outside L q hq (Even ((m : ℕ).factorization q.1)) F ?_
    (originalDegreeClass m) ?_
  · intro c hc
    by_cases hcn : c = originalDegreeClass n
    · subst hcn
      rw [evenClass_originalDegreeClass] at hc
      exact absurd hc.symm hdiff
    · exact hF c hcn
  · rw [evenClass_originalDegreeClass]

/-- For every composite `n ≥ 2` that is not a prime power, `weilDeltaKernel 1 n > 0` because
the prime term vanishes and `n ≥ 2` lies strictly past the plastic crossing `e^{3d} > e^d + 1`. -/
theorem weilDeltaKernel_one_pos_of_not_isPrimePow {n : ℕ} (hn2 : 2 ≤ n) (hpp : ¬ IsPrimePow n) :
    0 < weilDeltaKernel 1 n := by
  have hn0 : 0 < n := by omega
  have hne : 1 ≠ n := by omega
  have hoff : ArithmeticEffectivityTheory.weilPrimeKernel 1 n = 0 := by
    by_contra hnz
    rcases weilPrimeKernel_ne_zero hnz with ⟨_, hp1⟩ | ⟨hd, _⟩
    · rw [Nat.div_one] at hp1
      exact hpp hp1
    · have : n ≤ 1 := Nat.le_of_dvd one_pos hd
      omega
  rw [weilDeltaKernel_eq, hoff, sub_zero]
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hd : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have habs : |Real.log (1 : ℝ) - Real.log (n : ℝ)| = Real.log (n : ℝ) := by
    rw [Real.log_one, zero_sub, abs_neg, abs_of_pos hd]
  have hcosh : Real.cosh ((Real.log (1 : ℝ) - Real.log (n : ℝ)) / 2) =
      Real.cosh (Real.log (n : ℝ) / 2) := by
    rw [Real.log_one, zero_sub, neg_div, Real.cosh_neg]
  unfold archCompensation
  simp only [Nat.cast_one]
  rw [hcosh, habs]
  change 0 < 2 * Real.cosh (Real.log (n : ℝ) / 2) - archProfile (Real.log (n : ℝ))
  rw [compensation_pos_iff hd, Real.exp_log (by linarith)]
  nlinarith [sq_nonneg (n : ℝ)]

/-- **Arbitrarily high place-rank obstruction.** Given any `r + 1 ≥ 2` distinct primes `S` and any
word `L` of at most `r` primes, `primeWord L` vanishes between `[x_1]` and `[x_{∏ S}]`, whereas
Weil's off-diagonal kernel `weilDeltaKernel 1 (∏ S)` is strictly positive. -/
theorem primeWord_eq_zero_and_weilDeltaKernel_pos (L : List {p : ℕ // p.Prime})
    (S : Finset {p : ℕ // p.Prime}) (hcard : L.length < S.card) (hS2 : 2 ≤ S.card) :
    let N : ℕ+ := ⟨∏ p ∈ S, p.1, Finset.prod_pos fun p _ => p.2.pos⟩
    primeWord L (fun c => if c = originalDegreeClass N then 1 else 0)
        (originalDegreeClass 1) = 0 ∧
      0 < weilDeltaKernel 1 N := by
  intro N
  have hex : ∃ q ∈ S, q ∉ L := by
    by_contra hall
    push Not at hall
    have hsub : S ⊆ L.toFinset := fun q hq => List.mem_toFinset.mpr (hall q hq)
    have hle := (Finset.card_le_card hsub).trans (List.toFinset_card_le L)
    omega
  obtain ⟨q, hqS, hqL⟩ := hex
  have hfact : ∀ p ∈ S, (N : ℕ).factorization p.1 = 1 := by
    intro p hp
    have hsplit : (N : ℕ) = p.1 * ∏ r ∈ S.erase p, r.1 := by
      exact (Finset.mul_prod_erase S (fun r => r.1) hp).symm
    have hndvd : ¬ p.1 ∣ ∏ r ∈ S.erase p, r.1 := by
      intro hd
      obtain ⟨r, hr, hpr⟩ := Prime.exists_mem_finset_dvd p.2.prime hd
      have heq : p = r := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 r.2).mp hpr)
      exact (Finset.mem_erase.mp hr).1 heq.symm
    rw [hsplit, Nat.factorization_mul p.2.ne_zero
      (Finset.prod_ne_zero_iff.mpr fun r _ => r.2.ne_zero),
      p.2.factorization, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
  constructor
  · refine primeWord_eq_zero_of_odd_outside L q hqL ?_ _ (fun c hc => if_neg hc)
    rw [PNat.one_coe, one_mul, hfact q hqS]
    exact Nat.not_even_one
  · obtain ⟨p₁, hp₁, p₂, hp₂, hp₁₂⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hN2 : 2 ≤ (N : ℕ) := by
      have hp1_le : p₁.1 ≤ (N : ℕ) :=
        Nat.le_of_dvd N.pos (Finset.dvd_prod_of_mem (fun r => r.1) hp₁)
      exact p₁.2.two_le.trans hp1_le
    have hnpp : ¬ IsPrimePow (N : ℕ) := by
      intro hpp
      obtain ⟨r, k, hr, hk, hrk⟩ := (isPrimePow_nat_iff _).mp hpp
      have hd₁ : p₁.1 ∣ r ^ k := hrk ▸ Finset.dvd_prod_of_mem (fun x => x.1) hp₁
      have hd₂ : p₂.1 ∣ r ^ k := hrk ▸ Finset.dvd_prod_of_mem (fun x => x.1) hp₂
      have he₁ := (Nat.prime_dvd_prime_iff_eq p₁.2 hr).mp (p₁.2.dvd_of_dvd_pow hd₁)
      have he₂ := (Nat.prime_dvd_prime_iff_eq p₂.2 hr).mp (p₂.2.dvd_of_dvd_pow hd₂)
      exact hp₁₂ (Subtype.ext (he₁.trans he₂.symm))
    exact weilDeltaKernel_one_pos_of_not_isPrimePow hN2 hnpp

/-! ## 3. Archimedean `SL₂(ℚ)`-leaf classification and Hecke disjointness -/

private theorem complex_rat_normSq (q : ℚ) : Complex.normSq (q : ℂ) = ((q ^ 2 : ℚ) : ℝ) := by
  simp [Complex.normSq_apply, sq]

private theorem arch_degree_eq (g : OppositeAdelic.RationalGroup) (m n : ℕ+)
    (he : h3Act (OppositeAdelic.archMap g)
        (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)) =
      degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) :
    ((m : ℕ) : ℚ) / (n : ℕ) = (g 1 0) ^ 2 * ((m : ℕ) : ℚ) ^ 2 + (g 1 1) ^ 2 := by
  have hd : h3Denom (OppositeAdelic.archMap g)
      (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)) =
      ((g 1 0 : ℚ) : ℝ) ^ 2 * ((m : ℕ) : ℝ) ^ 2 + ((g 1 1 : ℚ) : ℝ) ^ 2 := by
    simp only [h3Denom, degPoint, mul_zero, zero_add, ← Complex.normSq_eq_norm_sq]
    change Complex.normSq ((g 1 1 : ℚ) : ℂ) +
      Complex.normSq ((g 1 0 : ℚ) : ℂ) * ((m : ℕ) : ℝ) ^ 2 = _
    rw [complex_rat_normSq, complex_rat_normSq]
    push_cast
    ring
  have hD := h3Denom_pos (OppositeAdelic.archMap g)
    (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos))
  have ht := congrArg H3.t he
  rw [h3Act_t] at ht
  change ((m : ℕ) : ℝ) / _ = ((n : ℕ) : ℝ) at ht
  have hmul := (div_eq_iff hD.ne').mp ht
  rw [hd] at hmul
  have hr : ((m : ℕ) : ℝ) / (n : ℕ) =
      ((g 1 0 : ℚ) : ℝ) ^ 2 * ((m : ℕ) : ℝ) ^ 2 + ((g 1 1 : ℚ) : ℝ) ^ 2 := by
    apply (div_eq_iff (show ((n : ℕ) : ℝ) ≠ 0 by exact_mod_cast n.ne_zero)).mpr
    simpa only [mul_comm] using hmul
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact hr

/-- **Archimedean leaf classification.** Two degree points have `ℍ³` coordinates in the same
`SL₂(ℚ)`-orbit if and only if `m * n` is a sum of two squares in `ℕ`. -/
theorem same_arch_orbit_iff_sum_two_squares (m n : ℕ+) :
    (∃ γ : conjugateArithmeticGroup,
      (γ • originalDegreePoint n).1 = (originalDegreePoint m).1) ↔
    ∃ x y : ℕ, (m : ℕ) * n = x ^ 2 + y ^ 2 := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, hg⟩ := γ.property
    have ha : h3Act (OppositeAdelic.archMap g)
        (degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) =
      degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos) := by
      change ((γ : AdelicGroup) • originalDegreePoint n).1 = _ at hγ
      rw [← hg, conjugate_arithmetic_smul] at hγ
      exact hγ
    have heq := arch_degree_eq g n m ha
    set u : ℚ := g 1 0 * (n : ℕ)
    set v : ℚ := g 1 1
    have huv : ((m : ℕ) : ℚ) * (n : ℕ) * (u ^ 2 + v ^ 2) = (n : ℕ) ^ 2 := by
      have hm0 : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
      have h1 : (n : ℕ) / ((m : ℕ) : ℚ) = u ^ 2 + v ^ 2 := by
        dsimp only [u, v]
        linarith [heq]
      calc ((m : ℕ) : ℚ) * (n : ℕ) * (u ^ 2 + v ^ 2)
          = ((m : ℕ) : ℚ) * (n : ℕ) * ((n : ℕ) / ((m : ℕ) : ℚ)) := by rw [← h1]
        _ = (n : ℕ) ^ 2 := by field_simp [hm0]
    let d : ℕ := u.den * v.den
    have hd0 : 0 < d := Nat.mul_pos u.den_pos v.den_pos
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hu_int : u * d = (u.num * (v.den : ℤ) : ℤ) := by
      dsimp only [d]
      push_cast
      calc u * ((u.den : ℚ) * v.den) = (u * u.den) * v.den := by ring
        _ = (u.num : ℚ) * v.den := by rw [Rat.mul_den_eq_num]
    have hv_int : v * d = (v.num * (u.den : ℤ) : ℤ) := by
      dsimp only [d]
      push_cast
      calc v * ((u.den : ℚ) * v.den) = (v * v.den) * u.den := by ring
        _ = (v.num : ℚ) * u.den := by rw [Rat.mul_den_eq_num]
    let A : ℕ := (u.num * (v.den : ℤ)).natAbs
    let B : ℕ := (v.num * (u.den : ℤ)).natAbs
    have hAB_Q : (A : ℚ) ^ 2 + (B : ℚ) ^ 2 = (u ^ 2 + v ^ 2) * (d : ℚ) ^ 2 := by
      have hA : ((A : ℚ) ^ 2) = (u * d) ^ 2 := by
        rw [hu_int]
        have : ((A : ℤ) : ℚ) ^ 2 = ((u.num * (v.den : ℤ) : ℤ) : ℚ) ^ 2 := by
          exact_mod_cast Int.natAbs_sq (u.num * (v.den : ℤ))
        simpa using this
      have hB : ((B : ℚ) ^ 2) = (v * d) ^ 2 := by
        rw [hv_int]
        have : ((B : ℤ) : ℚ) ^ 2 = ((v.num * (u.den : ℤ) : ℤ) : ℚ) ^ 2 := by
          exact_mod_cast Int.natAbs_sq (v.num * (u.den : ℤ))
        simpa using this
      rw [hA, hB]
      ring
    have hnat : ((m : ℕ) * n) * (A ^ 2 + B ^ 2) = ((n : ℕ) * d) ^ 2 := by
      apply Nat.cast_injective (R := ℚ)
      push_cast
      rw [hAB_Q]
      linear_combination ((d : ℚ) ^ 2) * huv
    have hAB_ne : A ^ 2 + B ^ 2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hnat
      exact (pow_ne_zero 2 (Nat.mul_ne_zero n.ne_zero hd0.ne')) hnat.symm
    rw [Nat.eq_sq_add_sq_iff]
    intro q hq hq3
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    haveI : Fact q.Prime := ⟨hqp⟩
    have hev_rhs : Even (padicValNat q (((n : ℕ) * d) ^ 2)) := by
      rw [padicValNat.pow ((n : ℕ) * d) 2]
      exact even_two_mul _
    rw [← hnat, padicValNat.mul (mul_ne_zero m.ne_zero n.ne_zero) hAB_ne] at hev_rhs
    have hev_AB : Even (padicValNat q (A ^ 2 + B ^ 2)) := by
      by_cases hmem : q ∈ (A ^ 2 + B ^ 2).primeFactors
      · exact Nat.eq_sq_add_sq_iff.mp ⟨A, B, rfl⟩ q hmem hq3
      · have hnd : ¬ q ∣ (A ^ 2 + B ^ 2) := fun hd =>
          hmem (Nat.mem_primeFactors.mpr ⟨hqp, hd, hAB_ne⟩)
        rw [padicValNat.eq_zero_of_not_dvd hnd]
        exact Even.zero
    rw [Nat.even_add] at hev_rhs
    exact hev_rhs.mpr hev_AB
  · rintro ⟨x, y, hxy⟩
    have hm0 : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
    have hn0 : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hxyQ : ((m : ℕ) : ℚ) * n = (x : ℚ) ^ 2 + (y : ℚ) ^ 2 := by exact_mod_cast hxy
    let c : ℚ := (x : ℚ) / ((m : ℕ) * n)
    let d : ℚ := (y : ℚ) / m
    let a : ℚ := ((m : ℕ) : ℚ) * d / n
    let b : ℚ := -(((m : ℕ) : ℚ) * n * c)
    have hsum : c ^ 2 * ((n : ℕ) : ℚ) ^ 2 + d ^ 2 = ((n : ℕ) : ℚ) / m := by
      dsimp only [c, d]
      calc ((x : ℚ) / ((m : ℕ) * n)) ^ 2 * (n : ℕ) ^ 2 + ((y : ℚ) / m) ^ 2
          = ((x : ℚ) ^ 2 + (y : ℚ) ^ 2) / ((m : ℕ) : ℚ) ^ 2 := by field_simp [hm0, hn0]
        _ = (((m : ℕ) : ℚ) * n) / ((m : ℕ) : ℚ) ^ 2 := by rw [← hxyQ]
        _ = ((n : ℕ) : ℚ) / m := by field_simp [hm0]
    have hdet : a * d - b * c = 1 := by
      dsimp only [a, b]
      calc ((m : ℕ) : ℚ) * d / n * d - -(((m : ℕ) : ℚ) * n * c) * c
          = ((m : ℕ) : ℚ) / n * (c ^ 2 * (n : ℕ) ^ 2 + d ^ 2) := by field_simp [hn0]; ring
        _ = ((m : ℕ) : ℚ) / n * (((n : ℕ) : ℚ) / m) := by rw [hsum]
        _ = 1 := by field_simp [hm0, hn0]
    have hz_num : b * d + a * c * ((n : ℕ) : ℚ) ^ 2 = 0 := by
      dsimp only [a, b]
      field_simp [hn0]
      ring
    let g : OppositeAdelic.RationalGroup := ⟨!![a, b; c, d], by
      rw [Matrix.det_fin_two]
      exact hdet⟩
    refine ⟨⟨conjugateEmbedding g, ⟨g, rfl⟩⟩, ?_⟩
    change (conjugateEmbedding g • originalDegreePoint n).1 = (originalDegreePoint m).1
    rw [conjugate_arithmetic_smul]
    change h3Act (OppositeAdelic.archMap g)
      (degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) =
      degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)
    have hDeq : h3Denom (OppositeAdelic.archMap g)
        (degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) = ((n : ℕ) : ℝ) / m := by
      simp only [h3Denom, degPoint, mul_zero, zero_add, ← Complex.normSq_eq_norm_sq]
      change Complex.normSq (d : ℂ) + Complex.normSq (c : ℂ) * ((n : ℕ) : ℝ) ^ 2 = _
      rw [complex_rat_normSq, complex_rat_normSq]
      have hsumR : ((c ^ 2 * ((n : ℕ) : ℚ) ^ 2 + d ^ 2 : ℚ) : ℝ) = (((n : ℕ) : ℚ) / m : ℚ) :=
        congrArg (fun r : ℚ => (r : ℝ)) hsum
      push_cast at hsumR ⊢
      linarith
    ext
    · rw [h3Act_z]
      change (((a : ℂ) * 0 + (b : ℂ)) * conj ((c : ℂ) * 0 + (d : ℂ)) +
        (a : ℂ) * conj (c : ℂ) * (((n : ℕ) : ℝ) : ℂ) ^ 2) / _ = 0
      rw [mul_zero, zero_add, mul_zero, zero_add, ← Complex.ofReal_ratCast d,
        ← Complex.ofReal_ratCast c, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.ofReal_ratCast, Complex.ofReal_ratCast, Complex.ofReal_natCast]
      have hnumC : (b : ℂ) * (d : ℂ) + (a : ℂ) * (c : ℂ) * ((n : ℕ) : ℂ) ^ 2 = 0 := by
        exact_mod_cast hz_num
      rw [hnumC, zero_div]
    · rw [h3Act_t, hDeq]
      change ((n : ℕ) : ℝ) / (((n : ℕ) : ℝ) / m) = (m : ℕ)
      field_simp [show ((n : ℕ) : ℝ) ≠ 0 by exact_mod_cast n.ne_zero,
        show ((m : ℕ) : ℝ) ≠ 0 by exact_mod_cast m.ne_zero]

/-- For every prime `p ≡ 3 (mod 4)`, `z_1` and `z_p` lie in disjoint `SL₂(ℚ)`-orbits in `ℍ³`, so
every word in the prime Hecke algebra `{A_q}_q` vanishes between `[x_1]` and `[x_p]`. -/
theorem primeWord_indicator_degree_eq_zero_of_mod_four (L : List {q : ℕ // q.Prime})
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    let P : ℕ+ := ⟨p, hp.pos⟩
    primeWord L (fun c => if c = originalDegreeClass P then 1 else 0)
      (originalDegreeClass 1) = 0 := by
  intro P
  let SameArch (c : ConjugateCarrier) : Prop :=
    Quotient.lift (fun x : GlobalSpace =>
      ∃ γ : conjugateArithmeticGroup, (γ • originalDegreePoint P).1 = x.1) (by
      intro x y h
      obtain ⟨γ₁, hγ₁⟩ := h
      apply propext
      constructor
      · rintro ⟨γ₂, hγ₂⟩
        refine ⟨γ₁⁻¹ * γ₂, ?_⟩
        have hy : y.1 = (γ₁⁻¹ • x).1 := by
          have := congrArg (fun z : GlobalSpace => (γ₁⁻¹ • z).1) hγ₁
          rwa [inv_smul_smul] at this
        rw [mul_smul, hy]
        exact congrArg (h3Act (γ₁⁻¹ : AdelicGroup).1) hγ₂
      · rintro ⟨γ₂, hγ₂⟩
        refine ⟨γ₁ * γ₂, ?_⟩
        have hx : (γ₁ • y).1 = x.1 := congrArg Prod.fst hγ₁
        rw [mul_smul, ← hx]
        exact congrArg (h3Act (γ₁ : AdelicGroup).1) hγ₂) c
  have hpres : ∀ M : List {q : ℕ // q.Prime}, ∀ c : ConjugateCarrier,
      ¬ SameArch c →
      primeWord M (fun d => if d = originalDegreeClass P then 1 else 0) c = 0 := by
    intro M
    induction M with
    | nil =>
      intro c hc
      change (if c = originalDegreeClass P then (1 : ℝ) else 0) = 0
      rw [if_neg]
      rintro rfl
      exact hc ⟨1, by rw [one_smul]⟩
    | cons q M ih =>
      intro c hc
      induction c using Quotient.inductionOn with
      | h x =>
        change primeOperator q (primeWord M _) (carrierClass x) = 0
        rw [primeOperator_apply]
        exact Finset.sum_eq_zero fun w _ => ih _ hc
  refine hpres L (originalDegreeClass 1) ?_
  intro hsame
  rw [show SameArch (originalDegreeClass 1) ↔
      ∃ γ : conjugateArithmeticGroup, (γ • originalDegreePoint P).1 = (originalDegreePoint 1).1
    from Iff.rfl, same_arch_orbit_iff_sum_two_squares, PNat.one_coe, one_mul,
    Nat.eq_sq_add_sq_iff] at hsame
  have hev : Even (padicValNat p p) :=
    hsame p (Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩) hp4
  rw [padicValNat.self hp.one_lt] at hev
  exact Nat.not_even_one hev

/-- **Single-step Hecke disjointness at every prime.** Even for `p = 2` or `p ≡ 1 (mod 4)`,
`primeOperator p` never connects `[x_1]` and `[x_p]`, because simultaneous integrality at `q ≠ p`
and single-step lattice transition at `p` force the bottom row of `g ∈ SL₂(ℚ)` into `ℤ²`,
contradicting `1 / p = g₁₀² + g₁₁²`. -/
theorem primeOperator_indicator_degree_eq_zero (p : {p : ℕ // p.Prime}) :
    let P : ℕ+ := ⟨p.1, p.2.pos⟩
    primeOperator p (fun c => if c = originalDegreeClass P then 1 else 0)
      (originalDegreeClass 1) = 0 := by
  intro P
  rw [show originalDegreeClass 1 = carrierClass (originalDegreePoint 1) from rfl,
    primeOperator_apply]
  refine Finset.sum_eq_zero fun v hv => ?_
  rw [if_neg]
  intro heq
  obtain ⟨γ, hγ⟩ := Quotient.exact heq
  obtain ⟨g, hg⟩ := γ.property
  have hstep : conjugateEmbedding g • originalDegreePoint P =
      replacePoint p (originalDegreePoint 1) v := by
    change (γ : AdelicGroup) • originalDegreePoint P = _ at hγ
    rwa [← hg] at hγ
  rw [conjugate_arithmetic_smul] at hstep
  have harch : h3Act (OppositeAdelic.archMap g)
      (degPoint ((P : ℕ) : ℝ) (by exact_mod_cast P.pos)) =
      degPoint ((1 : ℕ) : ℝ) (by norm_num) := congrArg Prod.fst hstep
  -- Use `g⁻¹` sending `z_1 ↦ z_p` so `1 / p = (g⁻¹ 1 0)² + (g⁻¹ 1 1)²`
  let h : OppositeAdelic.RationalGroup := g⁻¹
  have harch' : h3Act (OppositeAdelic.archMap h)
      (degPoint ((1 : ℕ) : ℝ) (by norm_num)) =
      degPoint ((P : ℕ) : ℝ) (by exact_mod_cast P.pos) := by
    dsimp only [h]
    rw [map_inv, ← harch, ← h3Act_mul, inv_mul_cancel, h3Act_one]
  have heq_rat := arch_degree_eq h 1 P harch'
  simp only [PNat.one_coe, Nat.cast_one, one_pow, mul_one] at heq_rat
  have hfin : (OppositeAdelic.weyl⁻¹ * h * OppositeAdelic.weyl) •
      (replaceVertex p (finitePoint (upperDegree 1)) v) = finitePoint (upperDegree P) := by
    have hf := congrArg Prod.snd hstep
    dsimp only [replacePoint, originalDegreePoint] at hf
    dsimp only [h]
    calc (OppositeAdelic.weyl⁻¹ * g⁻¹ * OppositeAdelic.weyl) •
          replaceVertex p (finitePoint (upperDegree 1)) v
        = (OppositeAdelic.weyl⁻¹ * g * OppositeAdelic.weyl)⁻¹ •
            ((OppositeAdelic.weyl⁻¹ * g * OppositeAdelic.weyl) • finitePoint (upperDegree P)) := by
          rw [hf]
          congr 1
          group
      _ = finitePoint (upperDegree P) := inv_smul_smul _ _
  have hbase1 : finitePoint (upperDegree 1) = finiteBase := by
    apply Subtype.ext
    funext q
    change QuotientGroup.mk (ProjGenLinGroup.mk (localGLMap q (upperDegree 1))) = baseVertex q
    have hu1 : upperDegree 1 = 1 := by
      apply GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [upperDegree]
    rw [hu1, map_one, map_one]
    rfl
  -- Integrality of `h 1 0` and `h 1 1` at all primes `q ≠ p`
  have haway : ∀ q : {q : ℕ // q.Prime}, q ≠ p →
      ‖((h 1 0 : ℚ) : ℚ_[q.1])‖ ≤ 1 ∧ ‖((h 1 1 : ℚ) : ℚ_[q.1])‖ ≤ 1 := by
    intro q hqp
    have hq := congrArg (fun u : FiniteVertices => u.1 q) hfin
    change localProj q (OppositeAdelic.weyl⁻¹ * h * OppositeAdelic.weyl) •
      (replaceVertex p (finitePoint (upperDegree 1)) v).1 q =
      principalVertex (upperDegree P) q at hq
    rw [replaceVertex_away _ _ _ q hqp, hbase1] at hq
    have hP_away : principalVertex (upperDegree P) q = baseVertex q := by
      apply QuotientGroup.eq.mpr
      rw [mul_one, Subgroup.inv_mem_iff]
      have hndvd : ¬ q.1 ∣ p.1 := fun hd =>
        hqp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hd))
      have hp_norm : ‖(p.1 : ℚ_[q.1])‖ = 1 := by
        change ‖((p.1 : ℚ) : ℚ_[q.1])‖ = 1
        rw [Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff (p := q.1) p.1).mpr hndvd]
        exact Rat.cast_one
      refine integralPGL_of_entries_det_norm q (localGLMap q (upperDegree P)) (fun i j => ?_) ?_
      · fin_cases i <;> fin_cases j <;>
          simp [localGLMap_apply, upperDegree, P, hp_norm]
      · rw [Matrix.det_fin_two]
        simp [localGLMap_apply, upperDegree, P, hp_norm]
    rw [hP_away] at hq
    have hmem : localProj q (OppositeAdelic.weyl⁻¹ * h * OppositeAdelic.weyl) ∈ integralPGL q := by
      change QuotientGroup.mk (localProj q (OppositeAdelic.weyl⁻¹ * h * OppositeAdelic.weyl) * 1) =
        QuotientGroup.mk 1 at hq
      have hh := QuotientGroup.eq.mp hq
      rw [mul_one, mul_one, Subgroup.inv_mem_iff] at hh
      exact hh
    have hw_mem : localProj q OppositeAdelic.weyl ∈ integralPGL q :=
      integralSL_mem q _ (OppositeAdelic.weyl_integral q)
    have hh_mem : localProj q h ∈ integralPGL q := by
      have hconj : localProj q h = localProj q OppositeAdelic.weyl *
          localProj q (OppositeAdelic.weyl⁻¹ * h * OppositeAdelic.weyl) *
          (localProj q OppositeAdelic.weyl)⁻¹ := by
        simp only [← map_mul, ← map_inv]
        congr 1
        group
      rw [hconj]
      exact (integralPGL q).mul_mem ((integralPGL q).mul_mem hw_mem hmem)
        ((integralPGL q).inv_mem hw_mem)
    rw [localProj_toGL] at hh_mem
    have hdet1 : ‖(localGLMap q (SpecialLinearGroup.toGL h)).val.det‖ = 1 := by
      have hh_det := h.prop
      rw [Matrix.det_fin_two] at hh_det
      have hdet_eq : (localGLMap q (SpecialLinearGroup.toGL h)).val.det = 1 := by
        rw [Matrix.det_fin_two]
        change ((h 0 0 : ℚ) : ℚ_[q.1]) * ((h 1 1 : ℚ) : ℚ_[q.1]) -
          ((h 0 1 : ℚ) : ℚ_[q.1]) * ((h 1 0 : ℚ) : ℚ_[q.1]) = 1
        exact_mod_cast hh_det
      rw [hdet_eq, norm_one]
    have hb0 := quadratic_entry_bound q (localGLMap q (SpecialLinearGroup.toGL h)) hh_mem 1 0
    have hb1 := quadratic_entry_bound q (localGLMap q (SpecialLinearGroup.toGL h)) hh_mem 1 1
    rw [hdet1] at hb0 hb1
    change ‖((h 1 0 : ℚ) : ℚ_[q.1])‖ ^ 2 ≤ 1 at hb0
    change ‖((h 1 1 : ℚ) : ℚ_[q.1])‖ ^ 2 ≤ 1 at hb1
    exact ⟨by nlinarith [norm_nonneg ((h 1 0 : ℚ) : ℚ_[q.1])],
      by nlinarith [norm_nonneg ((h 1 1 : ℚ) : ℚ_[q.1])]⟩
  -- Integrality of `h 1 0` and `h 1 1` at `p` itself
  have hat_p : ‖((h 1 0 : ℚ) : ℚ_[p.1])‖ ≤ 1 ∧ ‖((h 1 1 : ℚ) : ℚ_[p.1])‖ ≤ 1 := by
    have hp_eq := congrArg (fun u : FiniteVertices => u.1 p) hfin
    change localProj p (OppositeAdelic.weyl⁻¹ * h * OppositeAdelic.weyl) •
      (replaceVertex p (finitePoint (upperDegree 1)) v).1 p =
      principalVertex (upperDegree P) p at hp_eq
    rw [replaceVertex_at] at hp_eq
    dsimp only [originalDegreePoint] at hv
    rw [hbase1] at hv
    have hv_adj : v ∈ MulAction.orbit (integralPGL p) (neighbor p none) := by
      rw [baseOrbit_eq_range, ← adjacent_base_iff, ← mem_neighbors]
      exact hv
    obtain ⟨k, rfl⟩ := hv_adj
    obtain ⟨u_int, hk⟩ := k.property
    -- Apply `weyl` at `p`: `weyl • upperDegree P = lowerDegree P = neighbor p none`
    have hwP : localProj p OppositeAdelic.weyl • principalVertex (upperDegree P) p =
        neighbor p none := by
      have hw_fin := congrArg (fun u : FiniteVertices => u.1 p) (weyl_finite_upperDegree P)
      change localProj p OppositeAdelic.weyl • principalVertex (upperDegree P) p =
        principalVertex (lowerDegree P) p at hw_fin
      rw [hw_fin]
      apply congrArg QuotientGroup.mk
      apply congrArg ProjGenLinGroup.mk
      apply GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [localGLMap_apply, lowerDegree, neighborRep, P]
    have hp_eq' := congrArg (fun w : LocalVertex p => localProj p OppositeAdelic.weyl • w) hp_eq
    rw [hwP, ← mul_smul, show localProj p OppositeAdelic.weyl *
        localProj p (OppositeAdelic.weyl⁻¹ * h * OppositeAdelic.weyl) =
        localProj p h * localProj p OppositeAdelic.weyl by
      simp only [← map_mul]; congr 1; group] at hp_eq'
    have hw_mem : localProj p OppositeAdelic.weyl ∈ integralPGL p :=
      integralSL_mem p _ (OppositeAdelic.weyl_integral p)
    obtain ⟨w_int, hw_int⟩ := hw_mem
    let m_int : GL (Fin 2) ℤ_[p.1] := w_int * u_int
    change (localProj p h * localProj p OppositeAdelic.weyl) •
      ((k : LocalPGL p) • neighbor p none) = neighbor p none at hp_eq'
    rw [← mul_smul] at hp_eq'
    have hprod_eq : (localProj p h * localProj p OppositeAdelic.weyl) * (k : LocalPGL p) =
        localProj p h * ProjGenLinGroup.mk (integralMap p m_int) := by
      rw [mul_assoc]
      congr 1
      change localProj p OppositeAdelic.weyl * (k : LocalPGL p) = _
      rw [← hw_int, ← hk]
      exact ((ProjGenLinGroup.mk.comp (integralMap p)).map_mul w_int u_int).symm
    rw [hprod_eq, localProj_toGL, ← map_mul] at hp_eq'
    set A : LocalGL p := localGLMap p (SpecialLinearGroup.toGL h) * integralMap p m_int
    have hM_mem : ProjGenLinGroup.mk ((neighborRep p none)⁻¹ * A * neighborRep p none) ∈
        integralPGL p := by
      change QuotientGroup.mk (ProjGenLinGroup.mk A * ProjGenLinGroup.mk (neighborRep p none)) =
        QuotientGroup.mk (ProjGenLinGroup.mk (neighborRep p none)) at hp_eq'
      have hh := QuotientGroup.eq.mp hp_eq'.symm
      simpa only [map_mul, map_inv, mul_assoc] using hh
    have hA_det : ‖A.val.det‖ = 1 := by
      dsimp only [A]
      rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, integralMap_det_norm, mul_one]
      have hh_det := h.prop
      rw [Matrix.det_fin_two] at hh_det
      have hdet_eq : (localGLMap p (SpecialLinearGroup.toGL h)).val.det = 1 := by
        rw [Matrix.det_fin_two]
        change ((h 0 0 : ℚ) : ℚ_[p.1]) * ((h 1 1 : ℚ) : ℚ_[p.1]) -
          ((h 0 1 : ℚ) : ℚ_[p.1]) * ((h 1 0 : ℚ) : ℚ_[p.1]) = 1
        exact_mod_cast hh_det
      rw [hdet_eq, norm_one]
    have hM_det : ‖((neighborRep p none)⁻¹ * A * neighborRep p none).val.det‖ = 1 := by
      have hp0 : (p.1 : ℚ_[p.1]) ≠ 0 := by exact_mod_cast p.2.ne_zero
      rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.det_mul,
        Matrix.det_mul, GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv,
        Ring.inverse_eq_inv, neighborRep_det]
      have : (p.1 : ℚ_[p.1])⁻¹ * A.val.det * p.1 = A.val.det := by field_simp [hp0]
      rw [this, hA_det]
    have hb0 := quadratic_entry_bound p _ hM_mem 1 0
    have hb1 := quadratic_entry_bound p _ hM_mem 1 1
    rw [hM_det] at hb0 hb1
    have hA10 : ‖A 1 0‖ ≤ 1 := by
      have hentry : ((neighborRep p none)⁻¹ * A * neighborRep p none) 1 0 =
          A 1 0 / (p.1 : ℚ_[p.1]) := by
        change ((neighborRep p none).inv * A.val * (neighborRep p none).val) 1 0 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.mul_apply, Fin.sum_univ_two]
        simp [neighborRep, div_eq_mul_inv, mul_comm]
      rw [hentry, norm_div, Padic.norm_p] at hb0
      have hp1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast p.2.pos
      have hdiv : ‖A 1 0‖ / (p.1 : ℝ)⁻¹ ≤ 1 := by nlinarith [norm_nonneg (A 1 0)]
      rw [div_inv_eq_mul] at hdiv
      nlinarith [norm_nonneg (A 1 0)]
    have hA11 : ‖A 1 1‖ ≤ 1 := by
      have hentry : ((neighborRep p none)⁻¹ * A * neighborRep p none) 1 1 = A 1 1 := by
        have hp0 : (p.1 : ℚ_[p.1]) ≠ 0 := by exact_mod_cast p.2.ne_zero
        change ((neighborRep p none).inv * A.val * (neighborRep p none).val) 1 1 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.mul_apply, Fin.sum_univ_two]
        simp [neighborRep]
        field_simp [hp0]
      rw [hentry] at hb1
      nlinarith [norm_nonneg (A 1 1)]
    -- Multiply `A` on the right by `(integralMap p m_int⁻¹)` to recover the bottom row of `h`
    have hrec : localGLMap p (SpecialLinearGroup.toGL h) = A * integralMap p m_int⁻¹ := by
      dsimp only [A]
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hrow : ∀ j : Fin 2, ‖(localGLMap p (SpecialLinearGroup.toGL h)) 1 j‖ ≤ 1 := by
      intro j
      rw [hrec]
      change ‖(A.val * (integralMap p m_int⁻¹).val) 1 j‖ ≤ 1
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      exact (Padic.nonarchimedean _ _).trans (max_le
        (by rw [norm_mul]; exact mul_le_one₀ hA10 (norm_nonneg _) (m_int⁻¹ 0 j).2)
        (by rw [norm_mul]; exact mul_le_one₀ hA11 (norm_nonneg _) (m_int⁻¹ 1 j).2))
    exact ⟨hrow 0, hrow 1⟩
  obtain ⟨z₀, hz₀⟩ := OppositeAdelic.integer_of_all_local_norm_le_one (h 1 0) fun q =>
    if hqp : q = p then hqp ▸ hat_p.1 else (haway q hqp).1
  obtain ⟨z₁, hz₁⟩ := OppositeAdelic.integer_of_all_local_norm_le_one (h 1 1) fun q =>
    if hqp : q = p then hqp ▸ hat_p.2 else (haway q hqp).2
  rw [hz₀, hz₁] at heq_rat
  have hp0 : ((P : ℕ) : ℚ) ≠ 0 := by exact_mod_cast P.ne_zero
  have hint_eq : (1 : ℤ) = (p.1 : ℤ) * (z₀ ^ 2 + z₁ ^ 2) := by
    have hQ : (1 : ℚ) = (p.1 : ℚ) * ((z₀ : ℚ) ^ 2 + (z₁ : ℚ) ^ 2) := by
      have h1 := (div_eq_iff hp0).mp heq_rat
      simp only [P, PNat.mk_coe] at h1
      linarith
    exact_mod_cast hQ
  have hnn : 0 ≤ z₀ ^ 2 + z₁ ^ 2 := add_nonneg (sq_nonneg z₀) (sq_nonneg z₁)
  have hp2 : (2 : ℤ) ≤ p.1 := by exact_mod_cast p.2.two_le
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [← h0, mul_zero] at hint_eq
    omega
  · nlinarith

#print axioms same_finite_leaf_iff_isSquare
#print axioms primeWord_eq_zero_and_weilDeltaKernel_pos
#print axioms same_arch_orbit_iff_sum_two_squares
#print axioms primeWord_indicator_degree_eq_zero_of_mod_four
#print axioms primeOperator_indicator_degree_eq_zero

end GaloisForLFunctions.HyperbolicArakelovTheory.CarrierSeparation
