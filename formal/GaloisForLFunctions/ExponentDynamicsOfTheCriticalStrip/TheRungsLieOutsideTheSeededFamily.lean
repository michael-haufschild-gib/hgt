import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDegreeTwoCharacterOfTheCubeRootsOfTwoHasItsHodgeIndex
import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation

/-!
# The rungs lie outside the seeded family

E6 asks for a seed for the Grössencharacter rungs `L(w, ψ₆^k ψ)`, `k ≥ 1`, of the cubic tower. Every
seed proved so far is MMD's theorem for the finite-order Hecke characters of `ℚ(ω)`, moved by
identities of Dirichlet series (base change to `ℚ`, induction to Artin characters). A product of
finite-order `L`-functions has algebraic-integer Dirichlet coefficients. The rungs do not.

* **Coefficients** (`rungCoeff`, `grossenLFunction_eq_LSeries`): `L(w, ψ₆^k ψ) = Σ a_k(n) n^{−w}`,
  `a_k(n) = Σ_{N𝔞 = n} ψ₆(𝔞)^k ψ(𝔞)`, on `Re w > 1`.
* **The rung is not integral at a split prime** (`exists_not_isIntegral_rungCoeff`): at a prime
  `p ≡ 1 (3)` beyond the conductor, `p = ππ'` and `ψ₆(π) = π'^6/p^3`, so
  `a_k(p) = (ψ(π) π'^{6k} + ψ(π') π^{6k})/p^{3k}`. If it were an algebraic integer, so would be
  `π'^{6k}/π`, which lies in `ℚ(ω)`: `π ∣ π'^{6k}` in `ℤ[ω]`, impossible for distinct primes
  (`not_isIntegral_split`).
* **No identity with integral Dirichlet series** (`not_grossenLFunction_mul_LSeries_eq`): if `f, g`
  take algebraic-integer values and `g(1) = 1`, then `L(w, ψ₆^k ψ)·L(w, g) = L(w, f)` fails for some
  real `w > 1`; the coefficients at `p` would give `a_k(p) = f(p) − g(p)`.
* **The seeded family** (`not_grossenLFunction_mul_prod_eq`): no rung is a quotient of products of
  finite-order Hecke `L`-functions of `ℚ(ω)`. A seed for the rungs is not a transport of the seed
  of MMD; it has to see the infinity type.
-/

noncomputable section

open NumberField Complex Filter
open scoped ComplexConjugate nonZeroDivisors

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.AbsoluteGeometryOfSpecZ GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
open HeckeLFunctions FamilyContinuationTheory

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### Algebraic integers in `ℚ(ω)` -/

theorem isIntegral_ringComplex (a : O) : IsIntegral ℤ (ringComplex a) :=
  (Algebra.IsIntegral.isIntegral a).map ringComplex.toIntAlgHom

theorem isIntegral_of_pow_eq_one {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1) : IsIntegral ℤ x :=
  IsIntegral.of_pow hn (h ▸ isIntegral_one)

/-- An algebraic integer `y` with `a y = b` makes `a` divide `b` in `ℤ[ω]`: `b/a ∈ ℚ(ω)` is integral. -/
theorem dvd_of_isIntegral_mul_eq {a b : O} (ha : a ≠ 0) {y : ℂ} (hy : IsIntegral ℤ y)
    (h : ringComplex a * y = ringComplex b) : a ∣ b := by
  let L : K →+* ℂ := IsFractionRing.lift (A := O) ringComplex_injective
  have hL : ∀ x : O, L (algebraMap O K x) = ringComplex x := IsFractionRing.lift_algebraMap _
  have ha' : algebraMap O K a ≠ 0 :=
    fun h0 => ha (IsFractionRing.injective O K (by rw [h0, map_zero]))
  have hza : ringComplex a ≠ 0 := fun h0 => ha (ringComplex_injective (by rw [h0, map_zero]))
  have hx : L (algebraMap O K b / algebraMap O K a) = y := by
    rw [map_div₀, hL, hL, div_eq_iff hza, ← h, mul_comm]
  have hxi : IsIntegral ℤ (algebraMap O K b / algebraMap O K a) :=
    (isIntegral_algHom_iff L.toIntAlgHom L.injective).mp (hx ▸ hy)
  haveI : IsScalarTower ℤ O K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [eq_intCast (algebraMap ℤ K), eq_intCast (algebraMap ℤ O), map_intCast]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hxi.tower_top (A := O))
  exact ⟨c, IsFractionRing.injective O K (by rw [map_mul, hc, mul_comm, div_mul_cancel₀ _ ha'])⟩

/-- `|π|² = N(π)`. -/
theorem norm_ringComplex_sq (a : O) :
    ‖ringComplex a‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  by_cases ha : a = 0
  · subst ha
    simp
  · set c₀ := (Coordinates.coords a).1
    set c₁ := (Coordinates.coords a).2
    have hc : Coordinates.eval c₀ c₁ = a := Coordinates.eval_coords a
    rw [← hc, Coordinates.complex_norm_eval_sq, Ideal.absNorm_span_singleton, Coordinates.norm_eval]
    have hpos := Coordinates.coordinate_norm_pos c₀ c₁ (hc.symm ▸ ha)
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le]
    push_cast
    ring

theorem ringComplex_unit_pow_six (u : Oˣ) : ringComplex (u : O) ^ 6 = 1 := by
  have hu6 : u ^ 6 = 1 := by
    rw [← card_units_thirdCyclotomic K]
    exact pow_card_eq_one'
  rw [← map_pow, ← Units.val_pow_eq_pow_val, hu6, Units.val_one, map_one]

/-! ### The sextic character at a split prime -/

/-- If `ππ' = up` and `|π|² = p`, then `ψ₆(π) p³ = π'^6`: `π̄ = p/π = π'/u` and `u⁶ = 1`. -/
theorem elemPsiSix_mul_eq {π₁ π₂ : O} {u : Oˣ} {p : ℕ} (hp : 0 < p)
    (hprod : π₁ * π₂ = u * p) (h₁ : ‖ringComplex π₁‖ ^ 2 = p) :
    elemPsiSix π₁ * (p : ℂ) ^ 3 = ringComplex π₂ ^ 6 := by
  have hz : ringComplex π₁ * ringComplex π₂ = ringComplex u * p := by
    rw [← map_mul, hprod, map_mul, map_natCast]
  have hn : (‖ringComplex π₁‖ : ℂ) ^ 2 = p := by exact_mod_cast h₁
  have hconj : ringComplex π₁ * conj (ringComplex π₁) = p := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h₁, Complex.ofReal_natCast]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hz0 : ringComplex π₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hconj
    exact hp0 hconj.symm
  have hbar : conj (ringComplex π₁) * ringComplex u = ringComplex π₂ :=
    mul_left_cancel₀ hz0 (by linear_combination ringComplex u * hconj - hz)
  rw [elemPsiSix_apply, complexUnitConj_apply, div_pow,
    show (‖ringComplex π₁‖ : ℂ) ^ 6 = (p : ℂ) ^ 3 by rw [show 6 = 2 * 3 by rfl, pow_mul, hn],
    div_mul_cancel₀ _ (pow_ne_zero 3 hp0), ← hbar, mul_pow, ringComplex_unit_pow_six, mul_one]

/-- **At a split prime the rung coefficient is not an algebraic integer.** With `ππ' = up`,
`|π|² = |π'|² = p`, `π ∤ π'^{6k}` and roots of unity `ζ, ζ'`, the number
`ψ₆(π)^k ζ + ψ₆(π')^k ζ' = (ζ π'^{6k} + ζ' π^{6k})/p^{3k}` is not integral: otherwise
`π'^{6k}/π = ζ^{-1}(c p^{3k−1} π' u^{-1} − ζ' π^{6k−1})` would be. -/
theorem not_isIntegral_split {π₁ π₂ : O} {u : Oˣ} {p j : ℕ} (hp : 0 < p)
    (hprod : π₁ * π₂ = u * p) (h₁ : ‖ringComplex π₁‖ ^ 2 = p) (h₂ : ‖ringComplex π₂‖ ^ 2 = p)
    (hndvd : ¬ π₁ ∣ π₂ ^ (6 * (j + 1))) {ζ₁ ζ₂ : ℂ} {n : ℕ} (hn : 0 < n) (hζ₁ : ζ₁ ^ n = 1)
    (hζ₂ : IsIntegral ℤ ζ₂) :
    ¬ IsIntegral ℤ (elemPsiSix π₁ ^ (j + 1) * ζ₁ + elemPsiSix π₂ ^ (j + 1) * ζ₂) := by
  intro hc
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Nat.succ_eq_add_one] at hζ₁ hn
  have e₁ := elemPsiSix_mul_eq hp hprod h₁
  have e₂ := elemPsiSix_mul_eq (π₁ := π₂) (π₂ := π₁) hp (by rw [mul_comm, hprod]) h₂
  have hc_eq : (elemPsiSix π₁ ^ (j + 1) * ζ₁ + elemPsiSix π₂ ^ (j + 1) * ζ₂) *
      (p : ℂ) ^ (3 * (j + 1)) =
      ζ₁ * ringComplex π₂ ^ (6 * (j + 1)) + ζ₂ * ringComplex π₁ ^ (6 * (j + 1)) := by
    simp only [pow_mul]
    rw [← e₁, ← e₂]
    ring
  have hz : ringComplex π₁ * ringComplex π₂ = ringComplex u * p := by
    rw [← map_mul, hprod, map_mul, map_natCast]
  have hu6 := ringComplex_unit_pow_six u
  set c := elemPsiSix π₁ ^ (j + 1) * ζ₁ + elemPsiSix π₂ ^ (j + 1) * ζ₂
  set y' := c * (p : ℂ) ^ (3 * j + 2) * ringComplex π₂ * ringComplex u ^ 5 -
    ζ₂ * ringComplex π₁ ^ (6 * j + 5)
  have hp' : IsIntegral ℤ (p : ℂ) := by simpa using isIntegral_ringComplex (p : O)
  have hy' : IsIntegral ℤ y' :=
    (((hc.mul (hp'.pow _)).mul (isIntegral_ringComplex _)).mul
      ((isIntegral_ringComplex _).pow _)).sub (hζ₂.mul ((isIntegral_ringComplex _).pow _))
  have hzy : ringComplex π₁ * y' = ζ₁ * ringComplex π₂ ^ (6 * (j + 1)) := by
    simp only [y']
    linear_combination (c * (p : ℂ) ^ (3 * j + 2) * ringComplex u ^ 5) * hz +
      (c * (p : ℂ) ^ (3 * j + 3)) * hu6 + hc_eq
  have hζint := isIntegral_of_pow_eq_one hn hζ₁
  refine hndvd (dvd_of_isIntegral_mul_eq (a := π₁) ?_ (hy'.mul (hζint.pow m)) ?_)
  · rintro rfl
    rw [map_zero, norm_zero] at h₁
    have h0 : (p : ℝ) = 0 := by rw [← h₁]; norm_num
    exact hp.ne' (by exact_mod_cast h0)
  · rw [← mul_assoc, hzy, map_pow]
    linear_combination ringComplex π₂ ^ (6 * (j + 1)) * hζ₁

/-! ### The rung coefficients -/

variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

/-- The Dirichlet coefficients `a_k(n) = Σ_{N𝔞 = n} ψ₆(𝔞)^k ψ(𝔞)` of the rung. -/
def rungCoeff (k n : ℕ) : ℂ :=
  ∑ I ∈ idealsOfNorm K n, idealPsiSix I ^ k * primitiveIdealValue 𝔪 ψ I

/-- Grouping the absolutely convergent ideal sum of the rung by norm. -/
theorem hasSum_term_rungCoeff {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    HasSum (LSeries.term (rungCoeff 𝔪 ψ k) w) (grossenLFunction 𝔪 ψ k w) := by
  let f (I : Ideal O) : ℂ :=
    idealPsiSix I ^ k * primitiveIdealValue 𝔪 ψ I * (Ideal.absNorm I : ℂ) ^ (-w)
  have hf0 : f ⊥ = 0 := by
    simp only [f, idealPsiSix_bot, zero_pow (show k ≠ 0 by omega), zero_mul]
  have hsupport : Function.support f ⊆ ((Ideal O)⁰ : Set (Ideal O)) := by
    intro I hI
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    rw [hzero, Submodule.zero_eq_bot] at hI
    exact hI hf0
  have hall : HasSum f (grossenLFunction 𝔪 ψ k w) := by
    rw [grossenLFunction_eq_tsum_ideals 𝔪 ψ hk hw]
    exact (hasSum_subtype_iff_of_support_subset hsupport).mp
      (summable_norm_grossenIdealTerm 𝔪 ψ k hw).of_norm.hasSum
  have hgroup := hall.tsum_fiberwise Ideal.absNorm
  have hterm (n : ℕ) :
      (∑' I : (Ideal.absNorm : Ideal O → ℕ) ⁻¹' {n}, f I.1) =
      LSeries.term (rungCoeff 𝔪 ψ k) w n := by
    letI : Fintype {I : Ideal O // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).fintype
    change (∑' I : {I : Ideal O // Ideal.absNorm I = n}, f I) = _
    rw [tsum_fintype, ← Finset.sum_subtype (idealsOfNorm K n) (fun _ => mem_idealsOfNorm) f]
    by_cases hn : n = 0
    · subst n
      rw [LSeries.term_zero]
      apply Finset.sum_eq_zero
      intro I hI
      rw [Ideal.absNorm_eq_zero_iff.mp (mem_idealsOfNorm.mp hI)]
      exact hf0
    · rw [LSeries.term_of_ne_zero hn, rungCoeff, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro I hI
      simp only [f, mem_idealsOfNorm.mp hI, Complex.cpow_neg, div_eq_mul_inv]
  rw [funext hterm] at hgroup
  exact hgroup

theorem LSeriesSummable_rungCoeff {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (rungCoeff 𝔪 ψ k) w :=
  (hasSum_term_rungCoeff 𝔪 ψ hk hw).summable

/-- The rung is the Dirichlet series of `a_k` on `Re w > 1`. -/
theorem grossenLFunction_eq_LSeries {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    grossenLFunction 𝔪 ψ k w = LSeries (rungCoeff 𝔪 ψ k) w :=
  (hasSum_term_rungCoeff 𝔪 ψ hk hw).tsum_eq.symm

theorem idealsOfNorm_one : idealsOfNorm K 1 = {⊤} := by
  ext I
  rw [mem_idealsOfNorm, Ideal.absNorm_eq_one_iff, Finset.mem_singleton]

theorem rungCoeff_one (k : ℕ) : rungCoeff 𝔪 ψ k 1 = 1 := by
  rw [rungCoeff, idealsOfNorm_one, Finset.sum_singleton, idealPsiSix_top, one_pow, one_mul,
    ← Ideal.one_eq_top, map_one]

/-- A residue prime to the modulus is a unit. -/
theorem isUnit_mk_of_span_sup_eq_top {I : Ideal O} {a : O} (h : Ideal.span {a} ⊔ I = ⊤) :
    IsUnit (Ideal.Quotient.mk I a) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hz0 : Ideal.Quotient.mk I z = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hz
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ c, ?_⟩
  rw [← map_mul, mul_comm, show c * a = 1 - z by linear_combination hyz, map_sub, hz0, sub_zero,
    map_one]

/-- A multiplicative character takes roots of unity on units. -/
theorem mulChar_pow_card_eq_one {R : Type*} [CommRing R] (χ : MulChar R ℂ) {x : R}
    (hx : IsUnit x) : χ x ^ Nat.card Rˣ = 1 := by
  obtain ⟨v, rfl⟩ := hx
  rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]

/-- **The rung coefficient is not an algebraic integer at a split prime beyond the conductor.** -/
theorem exists_not_isIntegral_rungCoeff {k : ℕ} (hk : 1 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ ¬ IsIntegral ℤ (rungCoeff 𝔪 ψ k p) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set 𝔣 := heckeFiniteConductor 𝔪 ψ
  have hN : 0 < Ideal.absNorm 𝔣 :=
    Nat.pos_of_ne_zero fun h => heckeFiniteConductor_ne_bot 𝔪 ψ (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨p, hp, hNp, hp1⟩ := Nat.exists_prime_gt_modEq_one (Ideal.absNorm 𝔣) three_ne_zero
  have hp3 : p % 3 = 1 := hp1
  refine ⟨p, hp, ?_⟩
  obtain ⟨P₁, P₂, hne, hPP⟩ := Finset.card_eq_two.mp (card_idealsOfNorm_split hp hp3)
  have hN₁ : Ideal.absNorm P₁ = p := mem_idealsOfNorm.mp (by rw [hPP]; simp)
  have hN₂ : Ideal.absNorm P₂ = p := mem_idealsOfNorm.mp (by rw [hPP]; simp)
  haveI hm₁ := isMaximal_of_absNorm_eq hp hN₁
  haveI hm₂ := isMaximal_of_absNorm_eq hp hN₂
  set π₁ := Submodule.IsPrincipal.generator P₁
  set π₂ := Submodule.IsPrincipal.generator P₂
  have hs₁ : Ideal.span {π₁} = P₁ := Ideal.span_singleton_generator P₁
  have hs₂ : Ideal.span {π₂} = P₂ := Ideal.span_singleton_generator P₂
  have hn₁ : ‖ringComplex π₁‖ ^ 2 = p := by rw [norm_ringComplex_sq, hs₁, hN₁]
  have hn₂ : ‖ringComplex π₂‖ ^ 2 = p := by rw [norm_ringComplex_sq, hs₂, hN₂]
  -- `P₁P₂ = (p)`
  have hp₁ : (p : O) ∈ P₁ := by simpa [hN₁] using Ideal.absNorm_mem P₁
  have hp₂ : (p : O) ∈ P₂ := by simpa [hN₂] using Ideal.absNorm_mem P₂
  have hcop : P₁ ⊔ P₂ = ⊤ := Ideal.IsMaximal.coprime_of_ne hm₁ hm₂ hne
  have hprodI : Ideal.span {(p : O)} = P₁ * P₂ := by
    refine eq_of_le_of_absNorm_eq ?_ ?_ ?_
    · rw [Ideal.mul_eq_inf_of_coprime hcop, Ideal.span_singleton_le_iff_mem]
      exact ⟨hp₁, hp₂⟩
    · rw [absNorm_span_natCast, map_mul, hN₁, hN₂, sq]
    · rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
  obtain ⟨v, hv⟩ : Associated (π₁ * π₂) (p : O) := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_mul_span_singleton, hs₁,
      hs₂, hprodI]
  have hprod : π₁ * π₂ = ((v⁻¹ : Oˣ) : O) * p := by
    rw [← hv, mul_comm _ (_ * _), mul_assoc, Units.mul_inv, mul_one]
  -- `π₁ ∤ π₂^{6k}`: the primes are distinct
  have hndvd : ¬ π₁ ∣ π₂ ^ (6 * (j + 1)) := by
    intro hd
    have hmem : π₂ ^ (6 * (j + 1)) ∈ P₁ := hs₁ ▸ Ideal.mem_span_singleton.mpr hd
    have hle : P₂ ≤ P₁ := by
      rw [← hs₂, Ideal.span_singleton_le_iff_mem]
      exact hm₁.isPrime.mem_of_pow_mem _ hmem
    exact hne (hm₂.eq_of_le hm₁.ne_top hle).symm
  -- the values of `ψ` at `P₁, P₂` are roots of unity
  have hroot : ∀ {P : Ideal O}, Ideal.absNorm P = p → P.IsMaximal →
      primitiveIdealValue 𝔪 ψ P ^ Nat.card (O ⧸ 𝔣)ˣ = 1 := by
    intro P hNP hPm
    have hnle : ¬ 𝔣 ≤ P := by
      intro hle
      have hd := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [hNP] at hd
      exact absurd (Nat.le_of_dvd hN hd) (not_le.mpr hNp)
    have hsup : P ⊔ 𝔣 = ⊤ := by
      by_contra hsup
      exact hnle (le_sup_right.trans (hPm.eq_of_le hsup le_sup_left).symm.le)
    have hg : Submodule.IsPrincipal.generator P ≠ 0 := by
      intro h0
      apply hPm.ne_top
      have h := Ideal.span_singleton_generator P
      rw [h0, Ideal.span_singleton_zero] at h
      rw [← h] at hNP
      simp at hNP
      exact absurd hNP.symm hp.ne_zero
    have hspan := Ideal.span_singleton_generator P
    rw [← hspan, primitiveIdealValue_span_singleton 𝔪 ψ hg]
    exact mulChar_pow_card_eq_one _
      (isUnit_mk_of_span_sup_eq_top (by rw [hspan]; exact hsup))
  haveI : Finite (O ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 (heckeFiniteConductor_ne_bot 𝔪 ψ)
  have hcard : 0 < Nat.card (O ⧸ 𝔣)ˣ := Nat.card_pos
  rw [rungCoeff, hPP, Finset.sum_pair hne]
  exact not_isIntegral_split hp.pos hprod hn₁ hn₂ hndvd hcard (hroot hN₁ hm₁)
    (isIntegral_of_pow_eq_one hcard (hroot hN₂ hm₂))

/-! ### Identities of Dirichlet series -/

/-- The coefficient of a Dirichlet convolution at a prime. -/
theorem convolution_apply_prime {f g : ℕ → ℂ} {p : ℕ} (hp : p.Prime) :
    LSeries.convolution f g p = f 1 * g p + f p * g 1 := by
  rw [LSeries.convolution_def]
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), hp.divisors,
    Finset.sum_pair (Ne.symm hp.one_lt.ne'), Nat.div_one, Nat.div_self hp.pos]

theorem abscissaOfAbsConv_lt_top {F : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable F s) :
    LSeries.abscissaOfAbsConv F < ⊤ :=
  h.abscissaOfAbsConv_le.trans_lt (by simp)

/-- **No identity with integral Dirichlet series.** If `f, g` take algebraic-integer values and
`g(1) = 1`, the rung times `L(w, g)` is not `L(w, f)` on `w > 1`. -/
theorem not_grossenLFunction_mul_LSeries_eq {k : ℕ} (hk : 1 ≤ k) {f g : ℕ → ℂ}
    (hf : ∀ n, IsIntegral ℤ (f n)) (hg : ∀ n, IsIntegral ℤ (g n)) (hg1 : g 1 = 1)
    (hfs : ∀ w : ℝ, 1 < w → LSeriesSummable f w) (hgs : ∀ w : ℝ, 1 < w → LSeriesSummable g w) :
    ¬ ∀ w : ℝ, 1 < w → grossenLFunction 𝔪 ψ k w * LSeries g w = LSeries f w := by
  intro h
  obtain ⟨p, hp, hni⟩ := exists_not_isIntegral_rungCoeff 𝔪 ψ hk
  have hre : ∀ w : ℝ, 1 < w → 1 < (w : ℂ).re := fun w hw => by simpa using hw
  have hconv : ∀ w : ℝ, 1 < w →
      LSeries (LSeries.convolution (rungCoeff 𝔪 ψ k) g) w = LSeries f w := fun w hw => by
    rw [LSeries_convolution' (LSeriesSummable_rungCoeff 𝔪 ψ hk (hre w hw)) (hgs w hw),
      ← grossenLFunction_eq_LSeries 𝔪 ψ hk (hre w hw), h w hw]
  have h2 : (1 : ℝ) < 2 := one_lt_two
  have hcoef := LSeries.eq_of_LSeries_eventually_eq
    (abscissaOfAbsConv_lt_top ((LSeriesSummable_rungCoeff 𝔪 ψ hk (hre 2 h2)).convolution
      (hgs 2 h2)))
    (abscissaOfAbsConv_lt_top (hfs 2 h2))
    (Filter.eventually_atTop.mpr ⟨2, fun w hw => hconv w (by linarith)⟩) hp.ne_zero
  rw [convolution_apply_prime hp, hg1, mul_one, rungCoeff_one, one_mul] at hcoef
  apply hni
  rw [show rungCoeff 𝔪 ψ k p = f p - g p by linear_combination hcoef]
  exact (hf p).sub (hg p)

/-! ### The seeded family -/

/-- A finite-order Hecke character takes roots of unity or zero, so its coefficients are integral. -/
theorem isIntegral_heckeValue {𝔫 : Modulus K} (φ : HeckeCharacter 𝔫) (I : Ideal O) :
    IsIntegral ℤ (heckeValue 𝔫 φ I) := by
  unfold heckeValue
  split_ifs
  · refine isIntegral_of_pow_eq_one (n := Nat.card (RayClassGroup 𝔫)) Nat.card_pos ?_
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · exact isIntegral_zero

theorem isIntegral_heckeCoeff {𝔫 : Modulus K} (φ : HeckeCharacter 𝔫) (n : ℕ) :
    IsIntegral ℤ (heckeCoeff 𝔫 φ n) := by
  rw [heckeCoeff, ← mem_integralClosure_iff]
  exact Subalgebra.sum_mem _ fun I _ => isIntegral_heckeValue φ I

theorem heckeCoeff_one {𝔫 : Modulus K} (φ : HeckeCharacter 𝔫) : heckeCoeff 𝔫 φ 1 = 1 := by
  rw [heckeCoeff, idealsOfNorm_one, Finset.sum_singleton, ← Ideal.one_eq_top, heckeValue_one]

/-- The Dirichlet coefficients of a product of finite-order Hecke `L`-functions of `ℚ(ω)`. -/
def heckeProdCoeff : List (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) → ℕ → ℂ
  | [] => LSeries.delta
  | η :: A => LSeries.convolution (heckeCoeff η.1 η.2) (heckeProdCoeff A)

theorem isIntegral_convolution {f g : ℕ → ℂ} (hf : ∀ n, IsIntegral ℤ (f n))
    (hg : ∀ n, IsIntegral ℤ (g n)) (n : ℕ) : IsIntegral ℤ (LSeries.convolution f g n) := by
  rw [LSeries.convolution_def, ← mem_integralClosure_iff]
  exact Subalgebra.sum_mem _ fun x _ => (hf _).mul (hg _)

theorem isIntegral_heckeProdCoeff (A : List (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)) (n : ℕ) :
    IsIntegral ℤ (heckeProdCoeff A n) := by
  induction A generalizing n with
  | nil =>
    simp only [heckeProdCoeff, LSeries.delta]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  | cons η A ih => exact isIntegral_convolution (isIntegral_heckeCoeff η.2) ih n

theorem convolution_apply_one {f g : ℕ → ℂ} : LSeries.convolution f g 1 = f 1 * g 1 := by
  rw [LSeries.convolution_def]
  dsimp only
  rw [Nat.divisorsAntidiagonal_one, Finset.sum_singleton]

theorem heckeProdCoeff_one (A : List (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)) :
    heckeProdCoeff A 1 = 1 := by
  induction A with
  | nil => simp [heckeProdCoeff, LSeries.delta]
  | cons η A ih => rw [heckeProdCoeff, convolution_apply_one, heckeCoeff_one, ih, one_mul]

theorem LSeriesSummable_delta (s : ℂ) : LSeriesSummable LSeries.delta s :=
  (hasSum_single 1 fun n hn => by
    simp [LSeries.term, LSeries.delta, hn]).summable

theorem LSeriesSummable_heckeProdCoeff (A : List (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)) {w : ℂ}
    (hw : 1 < w.re) : LSeriesSummable (heckeProdCoeff A) w := by
  induction A with
  | nil => exact LSeriesSummable_delta w
  | cons η A ih => exact (lSeriesSummable_heckeCoeff η.1 η.2 hw).convolution ih

theorem LSeries_heckeProdCoeff (A : List (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)) {w : ℂ}
    (hw : 1 < w.re) :
    LSeries (heckeProdCoeff A) w = (A.map fun η => heckeL η.1 η.2 w).prod := by
  induction A with
  | nil => simp [heckeProdCoeff, LSeries_delta]
  | cons η A ih =>
    rw [heckeProdCoeff, LSeries_convolution' (lSeriesSummable_heckeCoeff η.1 η.2 hw)
      (LSeriesSummable_heckeProdCoeff A hw), ih, List.map_cons, List.prod_cons]
    rfl

/-- **No rung is a quotient of products of finite-order Hecke `L`-functions of `ℚ(ω)`.** -/
theorem not_grossenLFunction_mul_prod_eq {k : ℕ} (hk : 1 ≤ k)
    (A B : List (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)) :
    ¬ ∀ w : ℝ, 1 < w → grossenLFunction 𝔪 ψ k w * (B.map fun η => heckeL η.1 η.2 w).prod =
      (A.map fun η => heckeL η.1 η.2 w).prod := by
  intro h
  have hre : ∀ w : ℝ, 1 < w → 1 < (w : ℂ).re := fun w hw => by simpa using hw
  refine not_grossenLFunction_mul_LSeries_eq 𝔪 ψ hk (isIntegral_heckeProdCoeff A)
    (isIntegral_heckeProdCoeff B) (heckeProdCoeff_one B)
    (fun w hw => LSeriesSummable_heckeProdCoeff A (hre w hw))
    (fun w hw => LSeriesSummable_heckeProdCoeff B (hre w hw)) fun w hw => ?_
  rw [LSeries_heckeProdCoeff A (hre w hw), LSeries_heckeProdCoeff B (hre w hw)]
  exact h w hw

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
