import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.RittRationalLinearizerCocycle
import GaloisForLFunctions.HTGeometry.RittMeromorphicGermFrame

/-!
# The Ritt frame of formal Laurent series at a parabolic fixed point

Let `r = X·(1 + a X^k + X^{k+1} w)` be a formal power series with `a ≠ 0` and `k ≥ 1` — the
expansion
of a map tangent to the identity at a parabolic fixed point.  On the field of formal Laurent series,
realized as the fraction field of `ℂ⟦X⟧`:

* **substitution** `f ↦ f(r)` is a field endomorphism `σ`, extending the substitution of power
series
  (injective because `r` has order one);
* **the derivation** `d/dX` extends from power series, and obeys the chain rule `d(σ f) = r'·σ(d
f)`;
* **invariant series are constants**: if `f(r) = f`, compare the coefficient of `X^k` after clearing
  the order of `f` (`(m⁻ − m⁺)·a·g₀ = 0` forces order `0`), then the lowest term of `h(r) − h` for
  `h = f − f(0)`, which is `j·a·h_j X^{j+k}`.

The divisibility bookkeeping modulo powers of `X` carries all the coefficient computations.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Congruences modulo powers of `X` -/

theorem X_pow_dvd_pow_sub_one_sub {k : ℕ} (hk : 1 ≤ k) {a : ℂ} {w : ℂ⟦X⟧} (s : ℕ) :
    (X : ℂ⟦X⟧) ^ (k + 1)
      ∣ (1 + C a * X ^ k + X ^ (k + 1) * w) ^ s - (1 + C ((s : ℂ) * a) * X ^ k) := by
  induction s with
  | zero => simp
  | succ s ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(1 + C a * X ^ k + X ^ (k + 1) * w) * c + C ((s : ℂ) * a * a) * X ^ (k - 1)
        + w * (1 + C ((s : ℂ) * a) * X ^ k), ?_⟩
      have hkk : (X : ℂ⟦X⟧) ^ k * X ^ k = X ^ (k + 1) * X ^ (k - 1) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [pow_succ, ← sub_add_cancel ((1 + C a * X ^ k + X ^ (k + 1) * w) ^ s)
        (1 + C ((s : ℂ) * a) * X ^ k), hc]
      push_cast
      simp only [map_add, map_mul, map_natCast, map_one]
      linear_combination ((s : ℂ⟦X⟧) * C a * C a) * hkk

/-- The parabolic unit `u = 1 + a X^k + X^{k+1} w`. -/
def parUnit (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) : ℂ⟦X⟧ := 1 + C a * X ^ k + X ^ (k + 1) * w

/-- A parabolic germ `r = X·u`, tangent to the identity to order `k`. -/
def parGerm (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) : ℂ⟦X⟧ := X * parUnit k a w

variable {k : ℕ} {a : ℂ} {w : ℂ⟦X⟧}

theorem constantCoeff_parGerm : constantCoeff (parGerm k a w) = 0 := by
  simp [parGerm]

theorem hasSubst_parGerm : HasSubst (parGerm k a w) :=
  HasSubst.of_constantCoeff_zero constantCoeff_parGerm

theorem X_pow_dvd_parGerm_sub_X : (X : ℂ⟦X⟧) ^ (k + 1) ∣ parGerm k a w - X :=
  ⟨C a + X * w, by simp only [parGerm, parUnit]; ring⟩

/-- The substitution as an algebra endomorphism of power series. -/
def parSubst (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) : ℂ⟦X⟧ →ₐ[ℂ] ℂ⟦X⟧ :=
  substAlgHom (hasSubst_parGerm (k := k) (a := a) (w := w))

theorem parSubst_apply (f : ℂ⟦X⟧) : parSubst k a w f = subst (parGerm k a w) f := by
  rw [parSubst, coe_substAlgHom]

theorem parSubst_X : parSubst k a w X = parGerm k a w := substAlgHom_X _

/-- **Substitution is the identity modulo `X^{k+1}`.** -/
theorem X_pow_dvd_parSubst_sub (g : ℂ⟦X⟧) : (X : ℂ⟦X⟧) ^ (k + 1) ∣ parSubst k a w g - g := by
  set P : ℂ⟦X⟧ := ∑ i ∈ Finset.range (k + 1), C (coeff i g) * X ^ i with hP
  have hgP : (X : ℂ⟦X⟧) ^ (k + 1) ∣ g - P := by
    refine X_pow_dvd_iff.mpr fun m hm => ?_
    rw [map_sub, hP, map_sum]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hm), sub_self]
  obtain ⟨q, hq⟩ := hgP
  have hg : g = P + X ^ (k + 1) * q := by rw [← hq]; ring
  have hmono : ∀ i : ℕ, ∀ c : ℂ, (X : ℂ⟦X⟧) ^ (k + 1)
      ∣ parSubst k a w (C c * X ^ i) - C c * X ^ i := by
    intro i c
    have hC : parSubst k a w (C c) = C c := (parSubst k a w).commutes c
    rw [map_mul, map_pow, hC, parSubst_X, ← mul_sub]
    exact dvd_mul_of_dvd_right (X_pow_dvd_parGerm_sub_X.trans (sub_dvd_pow_sub_pow _ _ _)) _
  have htail : (X : ℂ⟦X⟧) ^ (k + 1)
      ∣ parSubst k a w (X ^ (k + 1) * q) - X ^ (k + 1) * q := by
    rw [map_mul, map_pow, parSubst_X, parGerm, mul_pow]
    exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (dvd_mul_right _ _)
  rw [hg, map_add, show parSubst k a w P + parSubst k a w (X ^ (k + 1) * q) - (P + X ^ (k + 1) * q)
      = (parSubst k a w P - P) + (parSubst k a w (X ^ (k + 1) * q) - X ^ (k + 1) * q) by ring]
  refine dvd_add ?_ htail
  rw [hP, map_sum, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => hmono i _

/-- **The lowest term of `h(r) − h`.**  If `X^j ∣ h`, then modulo `X^{j+k+1}`,
`h(r) − h ≡ j·a·h_j X^{j+k}`. -/
theorem X_pow_dvd_parSubst_sub_lead (hk : 1 ≤ k) {h : ℂ⟦X⟧} {j : ℕ} (hj : (X : ℂ⟦X⟧) ^ j ∣ h) :
    (X : ℂ⟦X⟧) ^ (j + k + 1)
      ∣ parSubst k a w h - h - C ((j : ℂ) * a * coeff j h) * X ^ (j + k) := by
  obtain ⟨h₁, rfl⟩ := hj
  have hcoeff : coeff j (X ^ j * h₁) = constantCoeff h₁ := by
    rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
  rw [hcoeff]
  obtain ⟨e₁, he₁⟩ := X_pow_dvd_pow_sub_one_sub hk (a := a) (w := w) j
  obtain ⟨e₂, he₂⟩ := X_pow_dvd_parSubst_sub (k := k) (a := a) (w := w) h₁
  obtain ⟨e₃, he₃⟩ : (X : ℂ⟦X⟧) ∣ h₁ - C (constantCoeff h₁) := by
    refine X_dvd_iff.mpr ?_
    simp
  have hu : parSubst k a w (X ^ j * h₁) = X ^ j * (parUnit k a w ^ j * parSubst k a w h₁) := by
    rw [map_mul, map_pow, parSubst_X, parGerm, mul_pow]
    ring
  refine ⟨e₁ * (h₁ + X ^ (k + 1) * e₂) + (1 + C ((j : ℂ) * a) * X ^ k) * e₂
    + C ((j : ℂ) * a) * e₃, ?_⟩
  have hu' : parUnit k a w ^ j = (1 + C ((j : ℂ) * a) * X ^ k) + X ^ (k + 1) * e₁ := by
    rw [parUnit, ← he₁]; ring
  have hs' : parSubst k a w h₁ = h₁ + X ^ (k + 1) * e₂ := by rw [← he₂]; ring
  have hh₁ : h₁ = C (constantCoeff h₁) + X * e₃ := by rw [← he₃]; ring
  rw [hu, hu', hs']
  conv_lhs => rw [show C ((j : ℂ) * a * constantCoeff h₁) = C ((j : ℂ) * a) * C (constantCoeff h₁)
    from map_mul _ _ _]
  have hX : (X : ℂ⟦X⟧) ^ (j + k + 1) = X ^ j * X ^ (k + 1) := by rw [← pow_add]; ring_nf
  have hX' : (X : ℂ⟦X⟧) ^ (j + k) = X ^ j * X ^ k := by rw [← pow_add]
  rw [hX, hX']
  linear_combination (C ((j : ℂ) * a) * X ^ j * X ^ k) * he₃

/-- The coefficient of `X^k` of `u^m·f`. -/
theorem coeff_parUnit_pow_mul (hk : 1 ≤ k) (m : ℕ) (f : ℂ⟦X⟧) :
    coeff k (parUnit k a w ^ m * f) = coeff k f + (m : ℂ) * a * constantCoeff f := by
  obtain ⟨e, he⟩ := X_pow_dvd_pow_sub_one_sub hk (a := a) (w := w) m
  have hu : parUnit k a w ^ m = 1 + C ((m : ℂ) * a) * X ^ k + X ^ (k + 1) * e := by
    rw [parUnit, ← he]; ring
  rw [hu, add_mul, add_mul, one_mul, map_add, map_add, mul_assoc, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
    coeff_X_pow_mul', if_neg (by omega)]
  ring

/-- **A power series fixed by the substitution and vanishing at `0` is zero.** -/
theorem eq_zero_of_parSubst_eq (hk : 1 ≤ k) (ha : a ≠ 0) {h : ℂ⟦X⟧} (h0 : constantCoeff h = 0)
    (hfix : parSubst k a w h = h) : h = 0 := by
  by_contra hne
  set j := h.order.toNat with hjdef
  have hdvd : (X : ℂ⟦X⟧) ^ j ∣ h := X_pow_order_dvd
  have hcoeff : coeff j h ≠ 0 := coeff_order hne
  have hj1 : j ≠ 0 := by
    intro hj0
    rw [hj0, coeff_zero_eq_constantCoeff_apply, h0] at hcoeff
    exact hcoeff rfl
  have hlead := X_pow_dvd_parSubst_sub_lead (w := w) (a := a) hk hdvd
  rw [hfix, sub_self, zero_sub] at hlead
  have hc := (X_pow_dvd_iff.mp hlead) (j + k) (by omega)
  rw [map_neg, coeff_C_mul_X_pow, if_pos rfl, neg_eq_zero] at hc
  have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast hj1
  exact hcoeff ((mul_eq_zero.mp hc).resolve_left (mul_ne_zero hjC ha))

/-- **Invariance up to a power of the unit forces equal exponents.** -/
theorem eq_of_parUnit_pow_mul_parSubst (hk : 1 ≤ k) (ha : a ≠ 0) {g : ℂ⟦X⟧}
    (hg0 : constantCoeff g ≠ 0) {m₁ m₂ : ℕ}
    (h : parUnit k a w ^ m₁ * parSubst k a w g = parUnit k a w ^ m₂ * g) : m₁ = m₂ := by
  have hc := congrArg (coeff k) h
  rw [coeff_parUnit_pow_mul hk, coeff_parUnit_pow_mul hk] at hc
  obtain ⟨e, he⟩ := X_pow_dvd_parSubst_sub (k := k) (a := a) (w := w) g
  have hk' : coeff k (parSubst k a w g) = coeff k g := by
    have := congrArg (coeff k) he
    rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at this
    exact sub_eq_zero.mp this
  have h0' : constantCoeff (parSubst k a w g) = constantCoeff g := by
    have := congrArg (coeff 0) he
    rw [map_sub, coeff_X_pow_mul', if_neg (by omega), coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply] at this
    exact sub_eq_zero.mp this
  rw [hk', h0'] at hc
  have : ((m₁ : ℂ) - m₂) * (a * constantCoeff g) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp this with h1 | h1
  · exact_mod_cast sub_eq_zero.mp h1
  · exact absurd h1 (mul_ne_zero ha hg0)

/-! ### The field of formal Laurent series -/

/-- Formal Laurent series, as the fraction field of formal power series. -/
abbrev FormalLaurent : Type := FractionRing ℂ⟦X⟧

theorem parUnit_constantCoeff (hk : 1 ≤ k) : constantCoeff (parUnit k a w) = 1 := by
  simp [parUnit, show k ≠ 0 by omega]

theorem parSubst_constantCoeff (g : ℂ⟦X⟧) :
    constantCoeff (parSubst k a w g) = constantCoeff g := by
  obtain ⟨e, he⟩ := X_pow_dvd_parSubst_sub (k := k) (a := a) (w := w) g
  have := congrArg (coeff 0) he
  rw [map_sub, coeff_X_pow_mul', if_neg (by omega), coeff_zero_eq_constantCoeff_apply,
    coeff_zero_eq_constantCoeff_apply] at this
  exact sub_eq_zero.mp this

theorem parGerm_ne_zero (hk : 1 ≤ k) : parGerm k a w ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  rw [parGerm, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, parUnit_constantCoeff hk,
    map_zero] at this
  exact one_ne_zero this

/-- **Substitution by a germ of order one is injective.** -/
theorem parSubst_injective (hk : 1 ≤ k) : Function.Injective (parSubst k a w) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hne
  have hdecomp : f = X ^ f.order.toNat * f.divXPowOrder := X_pow_order_mul_divXPowOrder.symm
  have hg0 : constantCoeff f.divXPowOrder ≠ 0 := by
    rw [constantCoeff_divXPowOrder]; exact coeff_order hne
  rw [hdecomp, map_mul, map_pow, parSubst_X] at hf
  rcases mul_eq_zero.mp hf with h | h
  · rcases eq_or_ne f.order.toNat 0 with h0 | h0
    · rw [h0, pow_zero] at h; exact absurd h one_ne_zero
    · exact parGerm_ne_zero hk ((pow_eq_zero_iff h0).mp h)
  · apply hg0
    rw [← parSubst_constantCoeff (k := k) (a := a) (w := w), h, map_zero]

/-- **Substitution on formal Laurent series.** -/
def laurentSubst (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) (hk : 1 ≤ k) : FormalLaurent →+* FormalLaurent :=
  IsFractionRing.lift (A := ℂ⟦X⟧)
    (g := (algebraMap ℂ⟦X⟧ FormalLaurent).comp (parSubst k a w).toRingHom)
    ((IsFractionRing.injective ℂ⟦X⟧ FormalLaurent).comp (parSubst_injective hk))

theorem laurentSubst_algebraMap (hk : 1 ≤ k) (f : ℂ⟦X⟧) :
    laurentSubst k a w hk (algebraMap ℂ⟦X⟧ FormalLaurent f)
      = algebraMap ℂ⟦X⟧ FormalLaurent (parSubst k a w f) :=
  IsFractionRing.lift_algebraMap _ f

/-- The derivation `d/dX` on power series, with values in Laurent series. -/
def laurentDeriv₀ : Derivation ℂ ℂ⟦X⟧ FormalLaurent :=
  (Algebra.linearMap ℂ⟦X⟧ FormalLaurent).compDer (d⁄dX ℂ)

/-- **The derivation of formal Laurent series.** -/
def laurentDeriv : Derivation ℂ FormalLaurent FormalLaurent :=
  GaloisForLFunctions.fractionRingDerivation laurentDeriv₀

theorem laurentDeriv_algebraMap (f : ℂ⟦X⟧) :
    laurentDeriv (algebraMap ℂ⟦X⟧ FormalLaurent f) = algebraMap ℂ⟦X⟧ FormalLaurent (d⁄dX ℂ f) := by
  rw [laurentDeriv, GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- **The chain rule for substitution.** -/
theorem laurentDeriv_laurentSubst (hk : 1 ≤ k) (x : FormalLaurent) :
    laurentDeriv (laurentSubst k a w hk x)
      = algebraMap ℂ⟦X⟧ FormalLaurent (d⁄dX ℂ (parGerm k a w))
        * laurentSubst k a w hk (laurentDeriv x) := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := ℂ⟦X⟧) x
  have hq0 : algebraMap ℂ⟦X⟧ FormalLaurent q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hsq0 : algebraMap ℂ⟦X⟧ FormalLaurent (parSubst k a w q) ≠ 0 := by
    rw [← laurentSubst_algebraMap hk]
    exact (map_ne_zero _).mpr hq0
  have hds : ∀ f : ℂ⟦X⟧, d⁄dX ℂ (parSubst k a w f)
      = parSubst k a w (d⁄dX ℂ f) * d⁄dX ℂ (parGerm k a w) := by
    intro f
    rw [parSubst_apply, parSubst_apply, derivative_subst ℂ hasSubst_parGerm]
  rw [map_div₀, laurentSubst_algebraMap hk, laurentSubst_algebraMap hk, Derivation.leibniz_div,
    Derivation.leibniz_div, laurentDeriv_algebraMap, laurentDeriv_algebraMap,
    laurentDeriv_algebraMap, laurentDeriv_algebraMap, hds, hds]
  simp only [smul_eq_mul, map_mul, map_sub, map_pow, map_inv₀, laurentSubst_algebraMap hk]
  field_simp

/-- **A Laurent series fixed by the substitution is a constant.** -/
theorem exists_eq_C_of_laurentSubst_eq (hk : 1 ≤ k) (ha : a ≠ 0) (y : FormalLaurent)
    (hfixy : laurentSubst k a w hk y = y) :
    ∃ c : ℂ, y = algebraMap ℂ⟦X⟧ FormalLaurent (C c) := by
  classical
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, by rw [map_zero, map_zero]⟩
  set ι := algebraMap ℂ⟦X⟧ FormalLaurent with hι
  have hιinj : Function.Injective ι := IsFractionRing.injective ℂ⟦X⟧ FormalLaurent
  -- the normal form `y = X^e · g` with `g(0) ≠ 0`
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := ℂ⟦X⟧) y
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; rw [map_zero, zero_div] at hy0; exact hy0 rfl
  have hunit : ∀ f : ℂ⟦X⟧, f ≠ 0 → IsUnit f.divXPowOrder := fun f hf => by
    rw [isUnit_iff_constantCoeff, constantCoeff_divXPowOrder]
    exact (coeff_order hf).isUnit
  obtain ⟨uq, huq⟩ := hunit q hq0
  set g : ℂ⟦X⟧ := p.divXPowOrder * ↑uq⁻¹ with hg
  set e : ℤ := (p.order.toNat : ℤ) - q.order.toNat with he
  have hXι : ι X ≠ 0 := by rw [hι]; exact (map_ne_zero_iff _ hιinj).mpr X_ne_zero
  have hform : ι p / ι q = ι X ^ e * ι g := by
    rw [hg, map_mul, he, zpow_sub₀ hXι, zpow_natCast, zpow_natCast]
    have hp' : ι p = ι X ^ p.order.toNat * ι p.divXPowOrder := by
      rw [← map_pow, ← map_mul, X_pow_order_mul_divXPowOrder]
    have hq' : ι q = ι X ^ q.order.toNat * ι ↑uq := by
      rw [← map_pow, ← map_mul, huq, X_pow_order_mul_divXPowOrder]
    have huinv : ι ↑uq⁻¹ = (ι ↑uq)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [hp', hq', huinv]
    field_simp
  have hg0 : constantCoeff g ≠ 0 := by
    rw [hg, map_mul, constantCoeff_divXPowOrder]
    exact mul_ne_zero (coeff_order hp0) (Units.ne_zero (uq⁻¹.map constantCoeff.toMonoidHom))
  rw [hform] at hy0 hfixy ⊢
  -- apply the substitution
  have hσX : laurentSubst k a w hk (ι X) = ι X * ι (parUnit k a w) := by
    rw [hι, laurentSubst_algebraMap hk, parSubst_X, parGerm, map_mul]
  rw [map_mul, map_zpow₀, hσX, mul_zpow, laurentSubst_algebraMap hk] at hfixy
  have hkey : ι (parUnit k a w) ^ e * ι (parSubst k a w g) = ι g := by
    have hXe : ι X ^ e ≠ 0 := zpow_ne_zero _ hXι
    exact mul_left_cancel₀ hXe (by rw [← hfixy]; ring)
  have hU0 : ι (parUnit k a w) ≠ 0 := by
    refine (map_ne_zero_iff _ hιinj).mpr fun h => ?_
    have := congrArg constantCoeff h
    rw [parUnit_constantCoeff hk, map_zero] at this
    exact one_ne_zero this
  -- split the exponent
  have hsplit : ι (parUnit k a w) ^ e.toNat * ι (parSubst k a w g)
      = ι (parUnit k a w) ^ (-e).toNat * ι g := by
    have he' : e = (e.toNat : ℤ) - ((-e).toNat : ℤ) := by omega
    rw [he', zpow_sub₀ hU0, zpow_natCast, zpow_natCast] at hkey
    field_simp at hkey
    linear_combination hkey
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul] at hsplit
  have hm := eq_of_parUnit_pow_mul_parSubst hk ha hg0 (hιinj hsplit)
  have he0 : e = 0 := by omega
  rw [he0, zpow_zero, one_mul] at hkey
  have hfix : parSubst k a w g = g := hιinj hkey
  have hC : parSubst k a w (C (constantCoeff g)) = C (constantCoeff g) :=
    (parSubst k a w).commutes _
  have hh := eq_zero_of_parSubst_eq (w := w) hk ha (h := g - C (constantCoeff g))
    (by simp) (by rw [map_sub, hfix, hC])
  refine ⟨constantCoeff g, ?_⟩
  rw [he0, zpow_zero, one_mul]
  exact congrArg ι (sub_eq_zero.mp hh)

/-! ### Rational functions inside formal Laurent series -/

theorem polynomial_toLaurent_injective :
    Function.Injective ((algebraMap ℂ⟦X⟧ FormalLaurent).comp
      (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* ℂ⟦X⟧)) :=
  (IsFractionRing.injective ℂ⟦X⟧ FormalLaurent).comp (Polynomial.coe_injective ℂ)

/-- The expansion of a rational function as a formal Laurent series. -/
def ratExpandZero : RatFunc ℂ →+* FormalLaurent :=
  IsFractionRing.lift (A := Polynomial ℂ) polynomial_toLaurent_injective

theorem ratExpandZero_algebraMap (p : Polynomial ℂ) :
    ratExpandZero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap ℂ⟦X⟧ FormalLaurent (p : ℂ⟦X⟧) :=
  IsFractionRing.lift_algebraMap _ p

instance : Algebra (RatFunc ℂ) FormalLaurent := ratExpandZero.toAlgebra

theorem algebraMap_ratFunc_formalLaurent (Q : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) FormalLaurent Q = ratExpandZero Q := rfl

theorem ratExpandZero_C (c : ℂ) :
    ratExpandZero (RatFunc.C c) = algebraMap ℂ⟦X⟧ FormalLaurent (C c) := by
  rw [← RatFunc.algebraMap_C, ratExpandZero_algebraMap, Polynomial.coe_C]

/-- **Expansion commutes with differentiation.** -/
theorem laurentDeriv_ratExpandZero (Q : RatFunc ℂ) :
    laurentDeriv (ratExpandZero Q) = ratExpandZero (ratFuncDeriv Q) := by
  have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr (RatFunc.denom_ne_zero Q)
  have hden' : ratExpandZero (algebraMap (Polynomial ℂ) (RatFunc ℂ) Q.denom) ≠ 0 :=
    (map_ne_zero _).mpr hden
  conv_lhs => rw [← RatFunc.num_div_denom Q]
  conv_rhs => rw [← RatFunc.num_div_denom Q]
  rw [ratFuncDeriv_div_general hden, ratFuncDeriv_algebraMap, ratFuncDeriv_algebraMap,
    map_div₀ ratExpandZero, map_div₀ ratExpandZero, Derivation.leibniz_div]
  rw [ratExpandZero_algebraMap] at hden' ⊢
  simp only [map_sub, map_mul, map_pow, ratExpandZero_algebraMap, laurentDeriv_algebraMap,
    derivative_coe, smul_eq_mul]
  field_simp

variable {R : RatFunc ℂ}

/-- **Expansion commutes with substitution**, when the germ is the expansion of `R`. -/
theorem laurentSubst_ratExpandZero (hk : 1 ≤ k) (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hRr : ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w)) (Q : RatFunc ℂ) :
    laurentSubst k a w hk (ratExpandZero Q) = ratExpandZero (ratFuncSubstitutionAlgHom R hR Q) := by
  have hext : (laurentSubst k a w hk).comp ratExpandZero
      = ratExpandZero.comp (ratFuncSubstitutionAlgHom R hR).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        RatFunc.algebraMap_C, ratFuncSubstitutionAlgHom_C, ratExpandZero_C]
      rw [laurentSubst_algebraMap hk]
      exact congrArg _ ((parSubst k a w).commutes c)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        RatFunc.algebraMap_X, ratFuncSubstitutionAlgHom_X, hRr]
      rw [← RatFunc.algebraMap_X, ratExpandZero_algebraMap, Polynomial.coe_X,
        laurentSubst_algebraMap hk, parSubst_X]
  exact RingHom.congr_fun hext Q

/-- **The Ritt frame of formal Laurent series at a parabolic fixed point.** -/
def laurentFrame (hk : 1 ≤ k) (ha : a ≠ 0) (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hRr : ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w)) :
    RittFrame (RatFunc ℂ) FormalLaurent where
  σ := laurentSubst k a w hk
  ψ := (ratFuncSubstitutionAlgHom R hR).toRingHom
  d := laurentDeriv
  dK := ratFuncDeriv
  ρ := ratFuncDeriv R
  comp := laurentSubst_ratExpandZero hk hR hRr
  fixed := fun y hy => by
    obtain ⟨c, hc⟩ := exists_eq_C_of_laurentSubst_eq hk ha y hy
    exact ⟨RatFunc.C c, by rw [algebraMap_ratFunc_formalLaurent, ratExpandZero_C, hc]⟩
  d_add := map_add laurentDeriv
  d_mul := fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  d_base := laurentDeriv_ratExpandZero
  ρ_ne := ratFuncDeriv_ne_zero_of_nonconst' hR
  chain := fun x => by
    show laurentDeriv (laurentSubst k a w hk x) = ratExpandZero (ratFuncDeriv R) * _
    rw [laurentDeriv_laurentSubst hk, ← laurentDeriv_ratExpandZero, hRr, laurentDeriv_algebraMap]

theorem laurentFrame_isRational (hk : 1 ≤ k) (ha : a ≠ 0) (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hRr : ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w)) :
    (laurentFrame hk ha hR hRr).IsRational R hR :=
  ⟨fun _ => rfl, fun _ => rfl, rfl⟩

/-- The derivation of formal Laurent series as a differential ring. -/
abbrev laurentDifferential : Differential FormalLaurent :=
  letI : Algebra ℤ FormalLaurent := Ring.toIntAlgebra _
  ⟨Derivation.restrictScalars ℤ laurentDeriv⟩

theorem laurent_differentialAlgebra :
    letI := ratFuncDerivDifferential
    letI := laurentDifferential
    DifferentialAlgebra (RatFunc ℂ) FormalLaurent := by
  letI := ratFuncDerivDifferential
  letI := laurentDifferential
  exact ⟨fun q => by
    show laurentDeriv (ratExpandZero q) = ratExpandZero (ratFuncDeriv q)
    exact laurentDeriv_ratExpandZero q⟩

/-- **Ritt's implication at a parabolic fixed point, for a formal eigen-coordinate.**  If a nonzero
formal Laurent series `v` satisfies `v(r) = v/R'` and is differentially algebraic over `ℂ(z)`, then
`R` carries a rational cocycle `A(R)·R'^N = β·A`. -/
theorem ratTransport_of_laurent_eigen (hk : 1 ≤ k) (ha : a ≠ 0)
    (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    (hRr : ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w)) {v : FormalLaurent}
    (hv0 : v ≠ 0) (hv : laurentSubst k a w hk v = ratExpandZero (ratFuncDeriv R)⁻¹ * v)
    (hDA : letI := ratFuncDerivDifferential
      letI := laurentDifferential
      DifferentialAlgebraicOver (RatFunc ℂ) v) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : ℂ, β ≠ 0 ∧ ∃ A : RatFunc ℂ, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  letI := ratFuncDerivDifferential
  letI := laurentDifferential
  haveI := laurent_differentialAlgebra
  have hdiff : (laurentFrame hk ha hR hRr).d
      = ⇑(Differential.deriv (R := FormalLaurent)) := by
    funext x; rfl
  exact (laurentFrame_isRational hk ha hR hRr).ratTransport_of_eigen_of_noFixedPoint hdiff hd hv0
    hv hDA

end

end GaloisForLFunctions.HTGeometry
