import GaloisForLFunctions.HTGeometry.DeformedCriticalObservation

/-!
# The postcritical reciprocal coefficient separates the deformed fibre

A pair that inverts over the horizon extends, by one further reciprocal coefficient, to a pair that
inverts one order beyond it — provided the constant term is a unit.  That coefficient is determined
by the relation

`[t^L](Z W - 1)  +  v · Z(0)  =  0`,

and the relation is all that is needed to separate two points of a fibre: reducing it modulo the
deformation ideal makes `v` a unit and forces two equal postcritical coefficients to have equal
constant terms.

So two points of a deformed fibre with distinct constant terms have distinct postcritical reciprocal
coefficients — the statement that one postcritical observation resolves the critical ambiguity.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- The coefficient of a shifted polynomial. -/
theorem coeff_X_pow_mul_eq {L d : ℕ} (H : S[X]) (h : L ≤ d) :
    ((X : S[X]) ^ L * H).coeff d = H.coeff (d - L) := by
  rw [mul_comm, Polynomial.coeff_mul_X_pow', if_pos h]

/-- **The postcritical reciprocal coefficient exists.**  If the constant term is a unit, a pair that
inverts over the horizon extends by one reciprocal coefficient to a pair that inverts one order
further. -/
theorem exists_postcritical_coefficient {L : ℕ} {Z W G : S[X]} (τ : S) (hL : 0 < L)
    (hG : Z * W - 1 = X ^ L * G) (hunit : IsUnit (Z.coeff 0)) :
    ∃ v : S, G.coeff 0 + τ * W.coeff 0 + v * Z.coeff 0 = 0 ∧
      (X : S[X]) ^ (L + 1)
        ∣ (Z + Polynomial.C τ * X ^ L) * (W + Polynomial.C v * X ^ L) - 1 := by
  obtain ⟨u, hu⟩ := hunit
  refine ⟨-((G.coeff 0 + τ * W.coeff 0) * (u⁻¹ : Sˣ)), ?_, ?_⟩
  · rw [neg_mul, ← hu, mul_assoc]
    simp
  · set v : S := -((G.coeff 0 + τ * W.coeff 0) * (u⁻¹ : Sˣ)) with hv
    have hsplit : (Z + Polynomial.C τ * X ^ L) * (W + Polynomial.C v * X ^ L) - 1
        = X ^ L * (G + Polynomial.C τ * W + Polynomial.C v * Z
          + Polynomial.C (τ * v) * X ^ L) := by
      rw [Polynomial.C_mul]
      linear_combination hG
    rw [hsplit, Polynomial.X_pow_dvd_iff]
    intro d hd
    rcases Nat.lt_or_ge d L with h | h
    · rw [mul_comm, Polynomial.coeff_mul_X_pow', if_neg (by omega)]
    · have hdL : d = L := by omega
      subst hdL
      rw [coeff_X_pow_mul_eq _ (le_refl _), Nat.sub_self, Polynomial.coeff_add,
        Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by omega), mul_zero, add_zero, hv]
      rw [neg_mul, ← hu, mul_assoc]
      simp

/-- **The defining relation of the postcritical coefficient.** -/
theorem postcritical_relation {L : ℕ} {Z W G : S[X]} {v τ : S} (hL : 0 < L)
    (hG : Z * W - 1 = X ^ L * G)
    (hv : (X : S[X]) ^ (L + 1)
      ∣ (Z + Polynomial.C τ * X ^ L) * (W + Polynomial.C v * X ^ L) - 1) :
    G.coeff 0 + τ * W.coeff 0 + v * Z.coeff 0 = 0 := by
  have hsplit : (Z + Polynomial.C τ * X ^ L) * (W + Polynomial.C v * X ^ L) - 1
      = X ^ L * (G + Polynomial.C τ * W + Polynomial.C v * Z
        + Polynomial.C (τ * v) * X ^ L) := by
    rw [Polynomial.C_mul]
    linear_combination hG
  rw [hsplit, Polynomial.X_pow_dvd_iff] at hv
  have hc := hv L (by omega)
  rwa [coeff_X_pow_mul_eq _ (le_refl _), Nat.sub_self, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 = L)),
    mul_zero, add_zero] at hc

/-- **The postcritical coefficient separates.**  Two points of a fibre whose truncated errors are
congruent to one and whose constant terms differ modulo an ideal have postcritical reciprocal
coefficients that differ modulo that ideal. -/
theorem postcritical_separates {I : Ideal S} {L : ℕ} {Z₀ W₀ G₀ Z₁ W₁ G₁ : S[X]} {v₀ v₁ τ : S}
    (hL : 0 < L) (hτ : τ ∈ I)
    (hG₀ : Z₀ * W₀ - 1 = X ^ L * G₀) (hG₁ : Z₁ * W₁ - 1 = X ^ L * G₁)
    (hG₀one : G₀.coeff 0 - 1 ∈ I) (hG₁one : G₁.coeff 0 - 1 ∈ I)
    (hv₀ : (X : S[X]) ^ (L + 1)
      ∣ (Z₀ + Polynomial.C τ * X ^ L) * (W₀ + Polynomial.C v₀ * X ^ L) - 1)
    (hv₁ : (X : S[X]) ^ (L + 1)
      ∣ (Z₁ + Polynomial.C τ * X ^ L) * (W₁ + Polynomial.C v₁ * X ^ L) - 1)
    (hsep : Z₀.coeff 0 - Z₁.coeff 0 ∉ I) :
    v₀ - v₁ ∉ I := by
  intro hcon
  refine hsep ?_
  have h₀ := postcritical_relation hL hG₀ hv₀
  have h₁ := postcritical_relation hL hG₁ hv₁
  -- modulo `I` the two relations read `1 + v (Z i)(0) = 0`
  have hkey : v₀ * (Z₀.coeff 0 - Z₁.coeff 0) ∈ I := by
    have hrw : v₀ * (Z₀.coeff 0 - Z₁.coeff 0)
        = (G₀.coeff 0 + τ * W₀.coeff 0 + v₀ * Z₀.coeff 0)
          - (G₁.coeff 0 + τ * W₁.coeff 0 + v₁ * Z₁.coeff 0)
          - (G₀.coeff 0 - 1) + (G₁.coeff 0 - 1) - (v₀ - v₁) * Z₁.coeff 0
          - τ * W₀.coeff 0 + τ * W₁.coeff 0 := by
      ring
    rw [hrw, h₀, h₁]
    refine Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.add_mem _ (Submodule.sub_mem _ ?_ hG₀one) hG₁one)
      (Ideal.mul_mem_right _ _ hcon)) (Ideal.mul_mem_right _ _ hτ))
      (Ideal.mul_mem_right _ _ hτ)
    simp
  -- `v₀` is invertible modulo `I`
  have hunit : ∃ w : S, w * v₀ - 1 ∈ I := by
    refine ⟨-Z₀.coeff 0, ?_⟩
    have hrw : -Z₀.coeff 0 * v₀ - 1
        = -(G₀.coeff 0 + τ * W₀.coeff 0 + v₀ * Z₀.coeff 0) + (G₀.coeff 0 - 1)
          + τ * W₀.coeff 0 := by
      ring
    rw [hrw, h₀, neg_zero, zero_add]
    exact Submodule.add_mem _ hG₀one (Ideal.mul_mem_right _ _ hτ)
  obtain ⟨w, hw⟩ := hunit
  have hfinal : Z₀.coeff 0 - Z₁.coeff 0
      = w * (v₀ * (Z₀.coeff 0 - Z₁.coeff 0)) - (w * v₀ - 1) * (Z₀.coeff 0 - Z₁.coeff 0) := by
    ring
  rw [hfinal]
  exact Submodule.sub_mem _ (Ideal.mul_mem_left _ _ hkey) (Ideal.mul_mem_right _ _ hw)

end GaloisForLFunctions.HTGeometry
