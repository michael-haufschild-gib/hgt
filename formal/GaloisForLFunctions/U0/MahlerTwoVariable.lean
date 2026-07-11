/-
# The two-variable Mahler substitution and its eigenvalue rigidity

The graded Mahler carrier restricts on each finite layer to the two-variable rational
function field `ℂ(s, ℓ)` with the substitution `s ↦ s²`, `ℓ ↦ 2ℓ`.  This module builds that
substitution on `RatFunc (RatFunc ℂ)` and proves the eigenvalue rigidity used to clear
`ℓ`-denominators of Mahler telescopers: a nonzero rational function `ρ(s)` with
`ρ(s²) = μ·ρ(s)` forces `μ = 1`, by comparing trailing degrees and trailing coefficients of
the cross-multiplied dilation identity.
-/
import Mathlib
import GaloisForLFunctions.U0.VelocityJetSeries

namespace GaloisForLFunctions

open Polynomial MahlerPolynomial

noncomputable section

/-! ## Trailing data of the dyadic dilation -/

theorem natTrailingDegree_expand_two {r : Polynomial ℂ} (hr : r ≠ 0) :
    (Polynomial.expand ℂ 2 r).natTrailingDegree = 2 * r.natTrailingDegree := by
  have hexp0 : Polynomial.expand ℂ 2 r ≠ 0 := by
    intro h
    apply hr
    apply Polynomial.expand_injective (n := 2) (by omega)
    rw [h, map_zero]
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_expand (by omega : 0 < 2), if_pos ⟨r.natTrailingDegree, by ring⟩]
    have hdm : 2 * r.natTrailingDegree / 2 = r.natTrailingDegree := by omega
    rw [hdm]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hr
  · have htc : (Polynomial.expand ℂ 2 r).coeff
        ((Polynomial.expand ℂ 2 r).natTrailingDegree) ≠ 0 :=
      Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hexp0
    rw [Polynomial.coeff_expand (by omega : 0 < 2)] at htc
    by_cases hdvd : 2 ∣ (Polynomial.expand ℂ 2 r).natTrailingDegree
    · rw [if_pos hdvd] at htc
      have hle := Polynomial.natTrailingDegree_le_of_ne_zero htc
      omega
    · rw [if_neg hdvd] at htc
      exact absurd rfl htc

theorem trailingCoeff_expand_two (r : Polynomial ℂ) :
    (Polynomial.expand ℂ 2 r).trailingCoeff = r.trailingCoeff := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero]
  · rw [Polynomial.trailingCoeff, natTrailingDegree_expand_two hr,
      Polynomial.coeff_expand (by omega : 0 < 2), if_pos ⟨r.natTrailingDegree, by ring⟩]
    have hdm : 2 * r.natTrailingDegree / 2 = r.natTrailingDegree := by omega
    rw [hdm, Polynomial.trailingCoeff]

/-! ## Eigenvalue rigidity of the dyadic substitution -/

/-- **Eigenvalue rigidity.**  A nonzero rational function with `ρ(s²) = μ·ρ(s)` forces
`μ = 1`: trailing degrees of the cross identity balance the numerator and denominator, and
trailing coefficients then cancel completely. -/
theorem mahler_eigen_eq_one {ρ : RatFunc ℂ} (hρ0 : ρ ≠ 0) {μ : ℂ}
    (h : mahlerHom 0 ρ = RatFunc.C μ * ρ) : μ = 1 := by
  classical
  set pn : Polynomial ℂ := ρ.num with hpn
  set pd : Polynomial ℂ := ρ.denom with hpd
  have hpn0 : pn ≠ 0 := RatFunc.num_ne_zero hρ0
  have hpd0 : pd ≠ 0 := ρ.denom_ne_zero
  set pn₂ : Polynomial ℂ := Polynomial.expand ℂ 2 pn with hpn₂
  set pd₂ : Polynomial ℂ := Polynomial.expand ℂ 2 pd with hpd₂
  have hpn₂0 : pn₂ ≠ 0 := by
    intro hz
    apply hpn0
    apply Polynomial.expand_injective (n := 2) (by omega)
    rw [← hpn₂, hz, map_zero]
  have hpd₂0 : pd₂ ≠ 0 := by
    intro hz
    apply hpd0
    apply Polynomial.expand_injective (n := 2) (by omega)
    rw [← hpd₂, hz, map_zero]
  have hcomp : ∀ r : Polynomial ℂ, r.comp (Polynomial.X ^ 2 + Polynomial.C 0) =
      Polynomial.expand ℂ 2 r := by
    intro r
    rw [map_zero, add_zero, ← Polynomial.expand_eq_comp_X_pow]
  have hmah : mahlerHom 0 ρ =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) pn₂ / algebraMap (Polynomial ℂ) (RatFunc ℂ) pd₂ := by
    conv_lhs => rw [← ρ.num_div_denom]
    rw [map_div₀, mahlerHom_algebraMap, mahlerHom_algebraMap, hcomp, hcomp]
  -- the cross identity
  have hE : pn₂ * pd = Polynomial.C μ * pn * pd₂ := by
    apply IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)
    have hCμ : (RatFunc.C μ : RatFunc ℂ) =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C μ) := (RatFunc.algebraMap_C μ).symm
    have hρnum : ρ = algebraMap (Polynomial ℂ) (RatFunc ℂ) pn /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) pd := ρ.num_div_denom.symm
    rw [hmah, hρnum, hCμ] at h
    have hpdne : algebraMap (Polynomial ℂ) (RatFunc ℂ) pd ≠ 0 :=
      RatFunc.algebraMap_ne_zero hpd0
    have hpd₂ne : algebraMap (Polynomial ℂ) (RatFunc ℂ) pd₂ ≠ 0 :=
      RatFunc.algebraMap_ne_zero hpd₂0
    push_cast [map_mul]
    field_simp at h
    linear_combination h
  -- μ is nonzero
  have hμ0 : μ ≠ 0 := by
    intro hz
    rw [hz] at hE
    simp only [map_zero, zero_mul] at hE
    exact (mul_ne_zero hpn₂0 hpd0) hE
  have hCμ0 : Polynomial.C μ ≠ 0 := by simpa using hμ0
  -- trailing degrees balance
  have hdeg := congrArg Polynomial.natTrailingDegree hE
  rw [Polynomial.natTrailingDegree_mul hpn₂0 hpd0,
    Polynomial.natTrailingDegree_mul (mul_ne_zero hCμ0 hpn0) hpd₂0,
    Polynomial.natTrailingDegree_mul hCμ0 hpn0, Polynomial.natTrailingDegree_C,
    natTrailingDegree_expand_two hpn0, natTrailingDegree_expand_two hpd0] at hdeg
  have hdeg_eq : pn.natTrailingDegree = pd.natTrailingDegree := by omega
  -- trailing coefficients cancel
  have htcC : (Polynomial.C μ).trailingCoeff = μ := by
    rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_C, Polynomial.coeff_C_zero]
  have htc := congrArg Polynomial.trailingCoeff hE
  rw [Polynomial.trailingCoeff_mul, Polynomial.trailingCoeff_mul,
    Polynomial.trailingCoeff_mul, htcC,
    trailingCoeff_expand_two, trailingCoeff_expand_two] at htc
  have htn : pn.trailingCoeff ≠ 0 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hpn0
  have htd : pd.trailingCoeff ≠ 0 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hpd0
  have hcancel : (1 : ℂ) * (pn.trailingCoeff * pd.trailingCoeff) =
      μ * (pn.trailingCoeff * pd.trailingCoeff) := by
    rw [one_mul]
    linear_combination htc
  have := mul_right_cancel₀ (mul_ne_zero htn htd) hcancel
  exact this.symm

/-! ## Reduced-fraction bookkeeping over an arbitrary field -/

section RatFuncRepr

variable {F : Type*} [Field F]

theorem ratFunc_num_mul_eq_of_repr {f : RatFunc F} {p q : Polynomial F} (hq0 : q ≠ 0)
    (hf : f = algebraMap (Polynomial F) (RatFunc F) p / algebraMap (Polynomial F) (RatFunc F) q) :
    f.num * q = p * f.denom := by
  have hqne : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq0
  have hdne : algebraMap (Polynomial F) (RatFunc F) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hnum : algebraMap (Polynomial F) (RatFunc F) f.num =
      f * algebraMap (Polynomial F) (RatFunc F) f.denom :=
    (div_eq_iff hdne).mp f.num_div_denom
  have hmap : algebraMap (Polynomial F) (RatFunc F) (f.num * q) =
      algebraMap (Polynomial F) (RatFunc F) (p * f.denom) := by
    rw [map_mul, map_mul, hnum, hf]
    field_simp
  exact IsFractionRing.injective (Polynomial F) (RatFunc F) hmap

theorem ratFunc_denom_dvd_of_repr {f : RatFunc F} {p q : Polynomial F} (hq0 : q ≠ 0)
    (hf : f = algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q) :
    f.denom ∣ q := by
  have hcross := ratFunc_num_mul_eq_of_repr hq0 hf
  have hdvd : f.denom ∣ f.num * q := Dvd.intro_left _ hcross.symm
  exact f.isCoprime_num_denom.symm.dvd_of_dvd_mul_left hdvd

/-- The reduced denominator of a sum divides the product of reduced denominators. -/
theorem ratFunc_denom_add_dvd (f g : RatFunc F) :
    (f + g).denom ∣ f.denom * g.denom := by
  apply ratFunc_denom_dvd_of_repr (p := f.num * g.denom + f.denom * g.num)
    (mul_ne_zero f.denom_ne_zero g.denom_ne_zero)
  have h1 : algebraMap (Polynomial F) (RatFunc F) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h2 : algebraMap (Polynomial F) (RatFunc F) g.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero g.denom_ne_zero
  rw [map_add, map_mul, map_mul, map_mul]
  conv_lhs => rw [← f.num_div_denom, ← g.num_div_denom]
  rw [div_add_div _ _ h1 h2]

end RatFuncRepr

/-! ## The two-variable Mahler substitution -/

/-- The coefficient field of the outer layer: rational functions in the base variable. -/
abbrev MahlerBase : Type := RatFunc ℂ

/-- The polynomial-level two-variable transform: coefficients through the Mahler
substitution, the outer variable scaled by two. -/
def twoVarPolyHom : Polynomial MahlerBase →+* Polynomial MahlerBase :=
  letI : Invertible (2 : MahlerBase) := invertibleOfNonzero two_ne_zero
  ((algEquivCMulXAddC (2 : MahlerBase) 0).toAlgHom.toRingHom).comp
    (Polynomial.mapRingHom (mahlerHom 0).toRingHom)

theorem twoVarPolyHom_injective : Function.Injective twoVarPolyHom := by
  letI : Invertible (2 : MahlerBase) := invertibleOfNonzero two_ne_zero
  intro a b h
  have h' : (algEquivCMulXAddC (2 : MahlerBase) 0)
      (Polynomial.map (mahlerHom 0).toRingHom a) =
      (algEquivCMulXAddC (2 : MahlerBase) 0)
      (Polynomial.map (mahlerHom 0).toRingHom b) := h
  have h1 := (algEquivCMulXAddC (2 : MahlerBase) 0).injective h'
  exact Polynomial.map_injective _ (mahlerHom 0).toRingHom.injective h1

theorem twoVarPolyHom_ne_zero {p : Polynomial MahlerBase} (hp : p ≠ 0) :
    twoVarPolyHom p ≠ 0 := by
  intro h
  exact hp (twoVarPolyHom_injective (by rw [h, map_zero]))

/-- The two-variable Mahler substitution on the layer field `ℂ(s)(ℓ)`. -/
def twoVarMahler : RatFunc MahlerBase →+* RatFunc MahlerBase :=
  RatFunc.mapRingHom twoVarPolyHom (by
    intro q hq
    rw [mem_nonZeroDivisors_iff_ne_zero] at hq
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact twoVarPolyHom_ne_zero hq)

theorem twoVarMahler_apply_div (p q : Polynomial MahlerBase) :
    twoVarMahler (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (twoVarPolyHom p) /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (twoVarPolyHom q) := by
  have hcoe : twoVarMahler (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      RatFunc.map twoVarPolyHom (by
        intro x hx
        rw [mem_nonZeroDivisors_iff_ne_zero] at hx
        rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
        exact twoVarPolyHom_ne_zero hx)
        (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
          algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) :=
    congrFun (RatFunc.coe_mapRingHom_eq_coe_map _ _) _
  rw [hcoe, RatFunc.map_apply_div]

/-- The two-variable transform acts on coefficients by the Mahler substitution and scales
the coefficient of `ℓ^i` by `2^i`. -/
theorem twoVarPolyHom_coeff (w : Polynomial MahlerBase) (i : ℕ) :
    (twoVarPolyHom w).coeff i = 2 ^ i * mahlerHom 0 (w.coeff i) := by
  letI : Invertible (2 : MahlerBase) := invertibleOfNonzero two_ne_zero
  set w' : Polynomial MahlerBase := Polynomial.map (mahlerHom 0).toRingHom w with hw'
  have hstep : twoVarPolyHom w = (algEquivCMulXAddC (2 : MahlerBase) 0) w' := rfl
  rw [hstep, algEquivCMulXAddC_apply, map_zero, add_zero]
  have hcomp : (Polynomial.aeval (Polynomial.C (2 : MahlerBase) * Polynomial.X)) w' =
      w'.comp (Polynomial.C 2 * Polynomial.X) := Polynomial.comp_eq_aeval.symm
  rw [hcomp, Polynomial.comp_eq_sum_left]
  rw [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  have hterm : ∀ j ∈ w'.support,
      (Polynomial.C (w'.coeff j) * (Polynomial.C (2 : MahlerBase) * Polynomial.X) ^ j).coeff i =
      if j = i then 2 ^ i * w'.coeff i else 0 := by
    intro j _
    rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_ne j i with rfl | hj
    · rw [if_pos rfl, if_pos rfl, mul_one, mul_comm]
    · rw [if_neg (by omega), if_neg hj, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite_eq' w'.support i (fun _ => 2 ^ i * w'.coeff i)]
  have hmapc : w'.coeff i = mahlerHom 0 (w.coeff i) := by
    rw [hw', Polynomial.coeff_map]
    rfl
  by_cases hi : i ∈ w'.support
  · rw [if_pos hi, hmapc]
  · rw [if_neg hi]
    rw [Polynomial.notMem_support_iff] at hi
    rw [hmapc] at hi
    rw [hi, mul_zero]

theorem twoVarPolyHom_X :
    twoVarPolyHom (Polynomial.X : Polynomial MahlerBase) =
      Polynomial.C 2 * Polynomial.X := by
  ext i
  rw [twoVarPolyHom_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X]
  rcases eq_or_ne i 1 with rfl | hi
  · rw [if_pos rfl, map_one]
    norm_num
  · rw [if_neg (fun h => hi h.symm), map_zero, mul_zero, mul_zero]

/-- No nontrivial power of two is one. -/
theorem two_pow_ne_one {n : ℕ} (hn : 0 < n) : ((2 : ℂ) ^ n) ≠ 1 := by
  intro h
  have hnorm : ((2 : ℝ) ^ n) = 1 := by
    have := congrArg norm h
    simpa [norm_pow] using this
  have : (1 : ℝ) < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  linarith

/-- **ℓ-denominator elimination.**  A rational function whose Mahler cocycle
`σk − k` has an `ℓ`-power denominator itself has an `ℓ`-power denominator: the reduced
denominator is associate to its own transform up to `ℓ`-powers, and eigenvalue rigidity
collapses the prime-to-`ℓ` part to a constant. -/
theorem twoVarMahler_telescoper_denom_pow {k w : RatFunc MahlerBase}
    (heq : twoVarMahler k - k = w) {r : ℕ} {P : Polynomial MahlerBase}
    (hw : w = algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) P /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (Polynomial.X ^ r)) :
    ∃ a : ℕ, k.denom = Polynomial.X ^ a := by
  classical
  set v : Polynomial MahlerBase := k.denom with hv
  set u : Polynomial MahlerBase := k.num with hu
  have hv0 : v ≠ 0 := k.denom_ne_zero
  have hXr0 : (Polynomial.X : Polynomial MahlerBase) ^ r ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have htw_repr : twoVarMahler k =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (twoVarPolyHom u) /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (twoVarPolyHom v) := by
    conv_lhs => rw [← k.num_div_denom]
    rw [twoVarMahler_apply_div]
  set A : Polynomial MahlerBase := (twoVarMahler k).denom with hA
  have hA_dvd : A ∣ twoVarPolyHom v :=
    ratFunc_denom_dvd_of_repr (twoVarPolyHom_ne_zero hv0) htw_repr
  have htwv_dvd_A : twoVarPolyHom v ∣ A := by
    have hcross := ratFunc_num_mul_eq_of_repr (twoVarPolyHom_ne_zero hv0) htw_repr
    have hdvd : twoVarPolyHom v ∣ twoVarPolyHom u * A :=
      ⟨(twoVarMahler k).num, by rw [← hcross]; ring⟩
    have hco : IsCoprime (twoVarPolyHom u) (twoVarPolyHom v) :=
      (k.isCoprime_num_denom).map twoVarPolyHom
    exact hco.symm.dvd_of_dvd_mul_left hdvd
  have hw_denom : w.denom ∣ Polynomial.X ^ r := ratFunc_denom_dvd_of_repr hXr0 hw
  have hkw : twoVarMahler k = k + w := by rw [← heq]; ring
  have hA_dvd2 : A ∣ v * Polynomial.X ^ r := by
    have h1 : A ∣ v * w.denom := by
      rw [hA, hkw]
      exact ratFunc_denom_add_dvd k w
    exact h1.trans (mul_dvd_mul_left v hw_denom)
  have hv_dvd2 : v ∣ A * Polynomial.X ^ r := by
    have hnegw : (-w).denom ∣ Polynomial.X ^ r := by
      apply ratFunc_denom_dvd_of_repr (p := -P) hXr0
      rw [hw, map_neg, neg_div]
    have hkform : k = twoVarMahler k + (-w) := by rw [← heq]; ring
    have h1 : v ∣ A * (-w).denom := by
      rw [hv, hkform]
      exact ratFunc_denom_add_dvd (twoVarMahler k) (-w)
    exact h1.trans (mul_dvd_mul_left A hnegw)
  have htwv_dvd : twoVarPolyHom v ∣ v * Polynomial.X ^ r := htwv_dvd_A.trans hA_dvd2
  have hv_dvd : v ∣ twoVarPolyHom v * Polynomial.X ^ r :=
    hv_dvd2.trans (mul_dvd_mul_right hA_dvd _)
  -- strip the ℓ-power part of the denominator
  set a : ℕ := Polynomial.rootMultiplicity 0 v with ha
  have hpow_dvd : (Polynomial.X : Polynomial MahlerBase) ^ a ∣ v := by
    have := Polynomial.pow_rootMultiplicity_dvd v 0
    rwa [map_zero, sub_zero] at this
  obtain ⟨v₁, hv₁⟩ := hpow_dvd
  have hv₁0 : v₁ ≠ 0 := by
    intro h
    apply hv0
    rw [hv₁, h, mul_zero]
  have hndvd : ¬ (Polynomial.X : Polynomial MahlerBase) ∣ v₁ := by
    intro ⟨c, hc⟩
    have hdvd : (Polynomial.X - Polynomial.C 0) ^ (a + 1) ∣ v := by
      rw [map_zero, sub_zero, hv₁, hc, pow_succ]
      exact ⟨c, by ring⟩
    exact Polynomial.pow_rootMultiplicity_not_dvd hv0 0 hdvd
  have hv₁coeff0 : v₁.coeff 0 ≠ 0 := by
    intro h
    exact hndvd (Polynomial.X_dvd_iff.mpr h)
  -- transform of the factorization
  have htwfact : twoVarPolyHom v =
      Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.X ^ a * twoVarPolyHom v₁ := by
    rw [hv₁, map_mul, map_pow, twoVarPolyHom_X, mul_pow, ← Polynomial.C_pow]
  have htwv₁coeff0 : (twoVarPolyHom v₁).coeff 0 ≠ 0 := by
    rw [twoVarPolyHom_coeff, pow_zero, one_mul]
    intro h
    exact hv₁coeff0 ((map_eq_zero_iff _ (mahlerHom 0).toRingHom.injective).mp h)
  have hntwdvd : ¬ (Polynomial.X : Polynomial MahlerBase) ∣ twoVarPolyHom v₁ := by
    intro hX
    exact htwv₁coeff0 (Polynomial.X_dvd_iff.mp hX)
  -- prime-to-ℓ parts are mutually divisible
  have hCunit : IsUnit (Polynomial.C ((2 : MahlerBase) ^ a)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero))
  have hdvd_unit : ∀ {b c : Polynomial MahlerBase} {ω : Polynomial MahlerBase},
      IsUnit ω → b ∣ ω * c → b ∣ c := by
    intro b c ω hω h
    rcases hω with ⟨ω', rfl⟩
    have h2 : b ∣ (↑ω'⁻¹ : Polynomial MahlerBase) * (↑ω' * c) := Dvd.dvd.mul_left h _
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2
  have hXcop : ∀ {b : Polynomial MahlerBase}, b.coeff 0 ≠ 0 →
      ∀ n : ℕ, IsCoprime b ((Polynomial.X : Polynomial MahlerBase) ^ n) := by
    intro b hb n
    apply IsCoprime.pow_right
    refine ⟨Polynomial.C (b.coeff 0)⁻¹, - (Polynomial.C (b.coeff 0)⁻¹ * b.divX), ?_⟩
    have hX := Polynomial.X_mul_divX_add b
    have hc : (Polynomial.C (b.coeff 0)⁻¹) * Polynomial.C (b.coeff 0) = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hb, Polynomial.C_1]
    linear_combination -(Polynomial.C (b.coeff 0)⁻¹) * hX + hc
  have hd1 : twoVarPolyHom v₁ ∣ v₁ := by
    have h1 : twoVarPolyHom v₁ ∣ v * Polynomial.X ^ r := by
      apply dvd_trans ?_ htwv_dvd
      rw [htwfact]
      exact ⟨Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.X ^ a, by ring⟩
    rw [hv₁] at h1
    have h2 : twoVarPolyHom v₁ ∣ Polynomial.X ^ (a + r) * v₁ := by
      have h3 : Polynomial.X ^ a * v₁ * Polynomial.X ^ r =
          Polynomial.X ^ (a + r) * v₁ := by
        rw [pow_add]
        ring
      rwa [h3] at h1
    exact (hXcop htwv₁coeff0 (a + r)).dvd_of_dvd_mul_left h2
  have hd2 : v₁ ∣ twoVarPolyHom v₁ := by
    have h1 : Polynomial.X ^ a * v₁ ∣
        Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.X ^ a * twoVarPolyHom v₁ *
          Polynomial.X ^ r := by
      rw [← htwfact, ← hv₁]
      exact hv_dvd
    have h2 : v₁ ∣ Polynomial.C ((2 : MahlerBase) ^ a) *
        (Polynomial.X ^ (a + r) * twoVarPolyHom v₁) := by
      have h3 : v₁ ∣ Polynomial.X ^ a * v₁ := Dvd.intro_left _ rfl
      apply h3.trans
      have h4 : Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.X ^ a * twoVarPolyHom v₁ *
          Polynomial.X ^ r =
          Polynomial.C ((2 : MahlerBase) ^ a) *
            (Polynomial.X ^ (a + r) * twoVarPolyHom v₁) := by
        rw [pow_add]
        ring
      rwa [h4] at h1
    have h5 : v₁ ∣ Polynomial.X ^ (a + r) * twoVarPolyHom v₁ := hdvd_unit hCunit h2
    have h6 : v₁ ∣ twoVarPolyHom v₁ * Polynomial.X ^ (a + r) := by
      rwa [mul_comm] at h5
    exact (hXcop hv₁coeff0 (a + r)).dvd_of_dvd_mul_right h6
  -- the prime-to-ℓ part is a scaling eigenvector, hence constant
  obtain ⟨ω, hω⟩ := associated_of_dvd_dvd hd2 hd1
  obtain ⟨ε, hεu, hεC⟩ := Polynomial.isUnit_iff.mp ω.isUnit
  have hfact : twoVarPolyHom v₁ = v₁ * Polynomial.C ε := by
    rw [← hω, hεC]
  have hcoeff_eq : ∀ i, (2 : MahlerBase) ^ i * mahlerHom 0 (v₁.coeff i) =
      v₁.coeff i * ε := by
    intro i
    have := congrArg (fun t : Polynomial MahlerBase => t.coeff i) hfact
    simpa [twoVarPolyHom_coeff, Polynomial.coeff_mul_C] using this
  have hsingle : ∀ i, v₁.coeff i ≠ 0 → i = 0 := by
    intro i hi
    by_contra hi0
    have h0' := hcoeff_eq 0
    have hi' := hcoeff_eq i
    rw [pow_zero, one_mul] at h0'
    have hkey : mahlerHom 0 (v₁.coeff 0) * v₁.coeff i =
        2 ^ i * (v₁.coeff 0 * mahlerHom 0 (v₁.coeff i)) := by
      linear_combination v₁.coeff i * h0' - v₁.coeff 0 * hi'
    have hφi : mahlerHom 0 (v₁.coeff i) ≠ 0 := fun h =>
      hi ((map_eq_zero_iff _ (mahlerHom 0).toRingHom.injective).mp h)
    have hρ : mahlerHom 0 (v₁.coeff 0 / v₁.coeff i) =
        RatFunc.C ((2 : ℂ) ^ i) * (v₁.coeff 0 / v₁.coeff i) := by
      rw [map_div₀]
      have hC2 : (RatFunc.C ((2 : ℂ) ^ i) : MahlerBase) = (2 : MahlerBase) ^ i := by
        rw [map_pow]
        congr 1
        exact map_ofNat RatFunc.C 2
      rw [hC2]
      field_simp
      linear_combination hkey
    have hρ0 : v₁.coeff 0 / v₁.coeff i ≠ 0 := div_ne_zero hv₁coeff0 hi
    have hone := mahler_eigen_eq_one hρ0 hρ
    exact two_pow_ne_one (by omega) hone
  have hdeg : v₁.natDegree = 0 := by
    by_contra h
    have hlc : v₁.coeff v₁.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hv₁0
    exact h (hsingle _ hlc)
  have hv₁C : v₁ = Polynomial.C (v₁.coeff 0) := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
  -- monicity pins the constant
  have hmonic := k.monic_denom
  have hlead : v.leadingCoeff = 1 := hmonic
  rw [hv₁, Polynomial.leadingCoeff_mul, (Polynomial.monic_X_pow a).leadingCoeff, one_mul] at hlead
  have hv₁lead : v₁.leadingCoeff = v₁.coeff 0 := by
    rw [Polynomial.leadingCoeff, hdeg]
  refine ⟨a, ?_⟩
  rw [hv₁, hv₁C]
  rw [hv₁lead] at hlead
  rw [hlead, Polynomial.C_1, mul_one]

/-- The two-variable transform of an `ℓ`-power. -/
theorem twoVarPolyHom_X_pow (a : ℕ) :
    twoVarPolyHom ((Polynomial.X : Polynomial MahlerBase) ^ a) =
      Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.X ^ a := by
  rw [map_pow, twoVarPolyHom_X, mul_pow, ← Polynomial.C_pow]

/-- **No two-variable Mahler telescoper.**  For `N ≥ 1` and a nonzero constant-coefficient
Laurent charge `Q/ℓ`, no rational function `k(s, ℓ)` satisfies
`σk − k = s^{2N}·Q(ℓ)/ℓ`. -/
theorem no_twoVarMahler_telescoper {N : ℕ} (hN : 0 < N) {Q : Polynomial MahlerBase}
    (hQ0 : Q ≠ 0) (hQc : ∀ i : ℕ, ∃ γ : ℂ, Q.coeff i = RatFunc.C γ)
    (k : RatFunc MahlerBase) :
    twoVarMahler k - k ≠
      RatFunc.C ((RatFunc.X : MahlerBase) ^ (2 * N)) *
        (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) Q /
          algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) Polynomial.X) := by
  intro heq
  classical
  set sN : MahlerBase := (RatFunc.X : MahlerBase) ^ (2 * N) with hsN
  have hsN0 : sN ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  -- the right side has an ℓ-power denominator
  have hwrepr : RatFunc.C sN *
      (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) Q /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) Polynomial.X) =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (Polynomial.C sN * Q) /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (Polynomial.X ^ 1) := by
    rw [map_mul, pow_one]
    have hC : (RatFunc.C sN : RatFunc MahlerBase) =
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (Polynomial.C sN) :=
      (RatFunc.algebraMap_C sN).symm
    have hXne' : algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
        (Polynomial.X : Polynomial MahlerBase) ≠ 0 :=
      RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
    rw [hC]
    field_simp
  obtain ⟨a, ha⟩ := twoVarMahler_telescoper_denom_pow heq hwrepr
  set U : Polynomial MahlerBase := k.num with hU
  have hkrepr : k = algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) U /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (Polynomial.X ^ a) := by
    rw [hU, ← ha]
    exact k.num_div_denom.symm
  have hXa0 : (Polynomial.X : Polynomial MahlerBase) ^ a ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hXane : algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
      ((Polynomial.X : Polynomial MahlerBase) ^ a) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hXa0
  have hXne : algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
      (Polynomial.X : Polynomial MahlerBase) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have h2a0 : (Polynomial.C ((2 : MahlerBase) ^ a) : Polynomial MahlerBase) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (pow_ne_zero a two_ne_zero)
  have h2ane : algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
      (Polynomial.C ((2 : MahlerBase) ^ a)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero h2a0
  have hσk : twoVarMahler k =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (twoVarPolyHom U) /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
          (Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.X ^ a) := by
    rw [hkrepr, twoVarMahler_apply_div, twoVarPolyHom_X_pow]
  have hE : Polynomial.X * twoVarPolyHom U -
      Polynomial.C ((2 : MahlerBase) ^ a) * (Polynomial.X * U) =
      Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.C sN * Q * Polynomial.X ^ a := by
    apply IsFractionRing.injective (Polynomial MahlerBase) (RatFunc MahlerBase)
    have hCs : (RatFunc.C sN : RatFunc MahlerBase) =
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (Polynomial.C sN) :=
      (RatFunc.algebraMap_C sN).symm
    rw [hσk, hkrepr, hCs] at heq
    have hprodne : algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
        (Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.X ^ a) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (mul_ne_zero h2a0 hXa0)
    rw [map_mul] at hprodne heq
    field_simp at heq
    simp only [map_mul, map_sub, map_pow] at heq ⊢
    linear_combination heq
  -- per-degree coefficient equations
  have hcoeffs : ∀ d : ℕ,
      (2 : MahlerBase) ^ d * mahlerHom 0 (U.coeff d) - (2 : MahlerBase) ^ a * U.coeff d =
      (2 : MahlerBase) ^ a * sN * (if a ≤ d + 1 then Q.coeff (d + 1 - a) else 0) := by
    intro d
    have h := congrArg (fun t : Polynomial MahlerBase => t.coeff (d + 1)) hE
    simp only [Polynomial.coeff_sub] at h
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
      twoVarPolyHom_coeff] at h
    have hrhs : (Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.C sN * Q *
        Polynomial.X ^ a).coeff (d + 1) =
        (2 : MahlerBase) ^ a * sN * (if a ≤ d + 1 then Q.coeff (d + 1 - a) else 0) := by
      rw [Polynomial.coeff_mul_X_pow']
      rcases Nat.lt_or_ge (d + 1) a with hlt | hle
      · rw [if_neg (by omega), if_neg (by omega), mul_zero]
      · rw [if_pos hle, if_pos hle, mul_assoc, Polynomial.coeff_C_mul,
          Polynomial.coeff_C_mul, mul_assoc]
    rw [hrhs] at h
    exact h
  -- a nonzero charge coefficient produces a one-variable telescoper
  have hmain : ∀ e : ℕ, Q.coeff e ≠ 0 → 1 ≤ e + a → False := by
    intro e he hea
    set d : ℕ := e + a - 1 with hd
    have hda : a ≤ d + 1 := by omega
    have hd1a : d + 1 - a = e := by omega
    have h := hcoeffs d
    rw [if_pos hda, hd1a] at h
    obtain ⟨γ, hγ⟩ := hQc e
    have hγ0 : γ ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hγ
      exact he hγ
    set μ : ℂ := (2 : ℂ) ^ d / (2 : ℂ) ^ a with hμ
    have hμ0 : μ ≠ 0 := div_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero)
    have hC2E : ∀ n : ℕ, ((2 : MahlerBase) ^ n) = RatFunc.C ((2 : ℂ) ^ n) := by
      intro n
      rw [map_pow]
      congr 1
      exact (map_ofNat RatFunc.C 2).symm
    have h2aE : ((2 : MahlerBase) ^ a) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hone : RatFunc.C μ * mahlerHom 0 (U.coeff d) - U.coeff d =
        RatFunc.C γ * RatFunc.X ^ (2 * N) := by
      have hCμ : (RatFunc.C μ : MahlerBase) = (2 : MahlerBase) ^ d / (2 : MahlerBase) ^ a := by
        rw [hμ, map_div₀, hC2E, hC2E]
      rw [hCμ]
      rw [hγ, hsN] at h
      field_simp
      linear_combination h
    exact no_ratFunc_dyadic_telescoper hμ0 hγ0 hN (U.coeff d) hone
  -- a usable nonzero coefficient exists
  have hex : ∃ e, Q.coeff e ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hQ0 (Polynomial.ext fun n => by rw [hall n, Polynomial.coeff_zero])
  obtain ⟨e, he⟩ := hex
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- without a pole, the level-zero charge coefficient must already vanish
    have h0 := congrArg (fun t : Polynomial MahlerBase => t.coeff 0) hE
    simp only [Polynomial.coeff_sub] at h0
    have hL1 : (Polynomial.X * twoVarPolyHom U).coeff 0 = 0 := by
      rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
    have hL2 : (Polynomial.C ((2 : MahlerBase) ^ a) * (Polynomial.X * U)).coeff 0 = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
        zero_mul, mul_zero]
    have hR : (Polynomial.C ((2 : MahlerBase) ^ a) * Polynomial.C sN * Q *
        Polynomial.X ^ a).coeff 0 = sN * Q.coeff 0 := by
      rw [ha0, pow_zero, pow_zero, Polynomial.C_1, one_mul, mul_one, Polynomial.coeff_C_mul]
    rw [hL1, hL2, hR] at h0
    have h0' : sN * Q.coeff 0 = 0 := by linear_combination -h0
    have hQ00 : Q.coeff 0 = 0 := by
      rcases mul_eq_zero.mp h0' with hc | hc
      · exact absurd hc hsN0
      · exact hc
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h1
      · exact absurd hQ00 he
      · omega
    exact hmain e he (by omega)
  · exact hmain e he (by omega)

end

end GaloisForLFunctions
