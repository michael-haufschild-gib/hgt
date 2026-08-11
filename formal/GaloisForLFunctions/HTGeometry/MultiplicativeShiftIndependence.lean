import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# Algebraic independence of multiplicative shift coordinates

An element `y` of a difference field with `σ(y) = q·y` and `q` in the base is a multiplicative
coordinate over that base.  A finite family of such coordinates is algebraically independent over
the base as soon as the base carries no solution of the corresponding multiplicative coboundary
equation: no `u ≠ 0` with `τ(u) = u·∏ qᵢ^{mᵢ}` for a nonzero integer vector `m`.

The proof is the minimal-support descent.  Applying the automorphism to a shortest annihilating
polynomial multiplies its coefficients by the corresponding monomials in `q`; subtracting the two
relations after normalizing one monomial gives a shorter annihilator, hence zero, and each surviving
coefficient ratio solves the excluded equation.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K : Type*} [Field K] {r : ℕ}

/-- The automorphism of the polynomial algebra induced by a base automorphism together with a
diagonal scaling of the variables. -/
def shiftScale' (tau : K →+* K) (q : Fin r → K) (P : MvPolynomial (Fin r) K) :
    MvPolynomial (Fin r) K :=
  ∑ e ∈ P.support, MvPolynomial.monomial e (tau (P.coeff e) * ∏ i : Fin r, q i ^ e i)

theorem coeff_shiftScale' (tau : K →+* K) (q : Fin r → K) (P : MvPolynomial (Fin r) K)
    (e : Fin r →₀ ℕ) :
    (shiftScale' tau q P).coeff e = tau (P.coeff e) * ∏ i : Fin r, q i ^ e i := by
  classical
  rw [shiftScale', MvPolynomial.coeff_sum]
  by_cases he : e ∈ P.support
  · rw [Finset.sum_eq_single e]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro f _ hf
      rw [MvPolynomial.coeff_monomial, if_neg hf]
    · intro hnot
      exact absurd he hnot
  · have hzero : P.coeff e = 0 := MvPolynomial.notMem_support_iff.mp he
    rw [hzero, map_zero, zero_mul]
    refine Finset.sum_eq_zero fun f hf => ?_
    have hfe : f ≠ e := fun h => he (h ▸ hf)
    rw [MvPolynomial.coeff_monomial, if_neg hfe]

theorem support_shiftScale (tau : K →+* K) (htau : Function.Injective tau)
    {q : Fin r → K} (hq : ∀ i, q i ≠ 0)
    (P : MvPolynomial (Fin r) K) : (shiftScale' tau q P).support = P.support := by
  classical
  ext e
  simp only [MvPolynomial.mem_support_iff, coeff_shiftScale']
  constructor
  · intro h hzero
    rw [hzero, map_zero, zero_mul] at h
    exact h rfl
  · intro h
    refine mul_ne_zero ?_ ?_
    · exact fun h0 => h (htau (by rw [h0, map_zero]))
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hq i)

/-- Evaluating the scaled polynomial at the coordinates is the automorphism of the evaluation. -/
theorem aeval_shiftScale {L : Type*} [Field L] [Algebra K L] (sigma : L →+* L) (tau : K →+* K)
    (hcomp : ∀ k : K, sigma (algebraMap K L k) = algebraMap K L (tau k))
    (y : Fin r → L) (q : Fin r → K)
    (hshift : ∀ i, sigma (y i) = algebraMap K L (q i) * y i)
    (P : MvPolynomial (Fin r) K) :
    MvPolynomial.aeval y (shiftScale' tau q P) = sigma (MvPolynomial.aeval y P) := by
  classical
  have hsupp : ∀ (f : Fin r → K) (e : Fin r →₀ ℕ),
      (∏ i : Fin r, f i ^ e i) = ∏ i ∈ e.support, f i ^ e i := by
    intro f e
    refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    have he : e i = 0 := by simpa [Finsupp.mem_support_iff] using hi
    rw [he, pow_zero]
  have hmono : ∀ (c : K) (e : Fin r →₀ ℕ),
      MvPolynomial.aeval y (MvPolynomial.monomial e (tau c * ∏ i : Fin r, q i ^ e i))
        = sigma (MvPolynomial.aeval y (MvPolynomial.monomial e c)) := by
    intro c e
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    rw [show (algebraMap K L) (tau c * ∏ i : Fin r, q i ^ e i)
        = algebraMap K L (tau c) * algebraMap K L (∏ i : Fin r, q i ^ e i) from map_mul _ _ _]
    rw [show sigma (algebraMap K L c * (e.prod fun i k => y i ^ k))
        = sigma (algebraMap K L c) * sigma (e.prod fun i k => y i ^ k) from map_mul _ _ _]
    rw [hcomp, mul_assoc]
    congr 1
    simp only [Finsupp.prod]
    rw [hsupp q e, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_pow, hshift, mul_pow]
  have hP : P = ∑ e ∈ P.support, MvPolynomial.monomial e (P.coeff e) :=
    (MvPolynomial.support_sum_monomial_coeff P).symm
  rw [shiftScale', map_sum]
  rw [show MvPolynomial.aeval y P
      = ∑ e ∈ P.support, MvPolynomial.aeval y (MvPolynomial.monomial e (P.coeff e)) by
    conv_lhs => rw [hP]
    rw [map_sum]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun e _ => hmono (P.coeff e) e

/-- **Multiplicative shift coordinates are algebraically independent.**  A family of nonzero
elements multiplied by base factors under a difference automorphism is algebraically independent
over the base whenever the base solves no multiplicative coboundary equation in those factors. -/
theorem algebraicIndependent_of_multiplicativeShift
    {L : Type*} [Field L] [Algebra K L] (sigma : L →+* L) (tau : K →+* K)
    (htau : Function.Injective tau)
    (hcomp : ∀ k : K, sigma (algebraMap K L k) = algebraMap K L (tau k))
    (y : Fin r → L) (q : Fin r → K) (hy : ∀ i, y i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (hshift : ∀ i, sigma (y i) = algebraMap K L (q i) * y i)
    (Hcob : ∀ (u : K) (m : Fin r → ℤ), u ≠ 0 → m ≠ 0 →
      tau u ≠ u * ∏ i : Fin r, q i ^ (m i)) :
    AlgebraicIndependent K y := by
  classical
  rw [algebraicIndependent_iff]
  intro P₀ hP₀eval
  by_contra hP₀ne
  have hex : ∃ n, ∃ P : MvPolynomial (Fin r) K,
      MvPolynomial.aeval y P = 0 ∧ P ≠ 0 ∧ P.support.card = n :=
    ⟨P₀.support.card, P₀, hP₀eval, hP₀ne, rfl⟩
  obtain ⟨P, hPeval, hPne, hPcard⟩ := Nat.find_spec hex
  have hmin : ∀ Q : MvPolynomial (Fin r) K, MvPolynomial.aeval y Q = 0 → Q ≠ 0 →
      Nat.find hex ≤ Q.support.card := by
    intro Q hQeval hQne
    exact Nat.find_min' hex ⟨Q, hQeval, hQne, rfl⟩
  obtain ⟨e₀, he₀⟩ : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hPne (MvPolynomial.support_eq_empty.mp h)
  have hc₀ : P.coeff e₀ ≠ 0 := MvPolynomial.mem_support_iff.mp he₀
  set S : MvPolynomial (Fin r) K := shiftScale' tau q P with hS
  have hSeval : MvPolynomial.aeval y S = 0 := by
    rw [hS, aeval_shiftScale sigma tau hcomp y q hshift P, hPeval, map_zero]
  set R : MvPolynomial (Fin r) K :=
    MvPolynomial.C (S.coeff e₀) * P - MvPolynomial.C (P.coeff e₀) * S with hR
  have hReval : MvPolynomial.aeval y R = 0 := by
    rw [hR, map_sub, map_mul, map_mul, hPeval, hSeval, mul_zero, mul_zero, sub_zero]
  have hRcoeff : ∀ e, R.coeff e = S.coeff e₀ * P.coeff e - P.coeff e₀ * S.coeff e := by
    intro e
    rw [hR, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
  have hRsupport : R.support ⊆ P.support.erase e₀ := by
    intro e he
    rw [Finset.mem_erase]
    constructor
    · intro hee
      subst hee
      rw [MvPolynomial.mem_support_iff, hRcoeff] at he
      exact he (by ring)
    · rw [MvPolynomial.mem_support_iff, hRcoeff] at he
      by_contra hnot
      have hPe : P.coeff e = 0 := MvPolynomial.notMem_support_iff.mp hnot
      have hSe : S.coeff e = 0 := by
        rw [hS, coeff_shiftScale', hPe, map_zero, zero_mul]
      rw [hPe, hSe, mul_zero, mul_zero, sub_zero] at he
      exact he rfl
  have hRzero : R = 0 := by
    by_contra hRne
    have hcard := hmin R hReval hRne
    have hlt : R.support.card < P.support.card := by
      have h1 : R.support.card ≤ (P.support.erase e₀).card :=
        Finset.card_le_card hRsupport
      have h2 : (P.support.erase e₀).card < P.support.card :=
        Finset.card_erase_lt_of_mem he₀
      omega
    omega
  -- every coefficient satisfies the multiplicative relation
  have hrel : ∀ e, S.coeff e₀ * P.coeff e = P.coeff e₀ * S.coeff e := by
    intro e
    have hzero := hRcoeff e
    rw [hRzero] at hzero
    simp only [MvPolynomial.coeff_zero] at hzero
    exact sub_eq_zero.mp hzero.symm
  by_cases hsingle : P.support = {e₀}
  · -- a single monomial cannot annihilate nonzero coordinates
    have hPmono : P = MvPolynomial.monomial e₀ (P.coeff e₀) := by
      conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
      rw [hsingle, Finset.sum_singleton]
    rw [hPmono, MvPolynomial.aeval_monomial] at hPeval
    have hprod : (e₀.prod fun i k => y i ^ k) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hy i)
    have hcoe : algebraMap K L (P.coeff e₀) ≠ 0 := by
      simpa using (map_ne_zero_iff _ (algebraMap K L).injective).mpr hc₀
    exact (mul_ne_zero hcoe hprod) hPeval
  · -- a second monomial produces a solution of the excluded equation
    obtain ⟨e, he, hee₀⟩ : ∃ e ∈ P.support, e ≠ e₀ := by
      by_contra hnot
      refine hsingle (Finset.eq_singleton_iff_unique_mem.mpr ⟨he₀, fun f hf => ?_⟩)
      by_contra hfe
      exact hnot ⟨f, hf, hfe⟩
    have hce : P.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    set u : K := P.coeff e / P.coeff e₀ with hu
    have hune : u ≠ 0 := div_ne_zero hce hc₀
    set m : Fin r → ℤ := fun i => (e₀ i : ℤ) - (e i : ℤ) with hm
    have hmne : m ≠ 0 := by
      intro h0
      apply hee₀
      ext i
      have : (e₀ i : ℤ) - (e i : ℤ) = 0 := congrFun h0 i
      omega
    refine Hcob u m hune hmne ?_
    have hSe₀ : S.coeff e₀ = tau (P.coeff e₀) * ∏ i : Fin r, q i ^ e₀ i := by
      rw [hS, coeff_shiftScale']
    have hSe : S.coeff e = tau (P.coeff e) * ∏ i : Fin r, q i ^ e i := by
      rw [hS, coeff_shiftScale']
    have hkey := hrel e
    rw [hSe₀, hSe] at hkey
    have hq₀ : (∏ i : Fin r, q i ^ e₀ i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hq i)
    have hqe : (∏ i : Fin r, q i ^ e i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hq i)
    have htau₀ : tau (P.coeff e₀) ≠ 0 := fun h0 => hc₀ (htau (by rw [h0, map_zero]))
    have hzpow : (∏ i : Fin r, q i ^ (m i))
        = (∏ i : Fin r, q i ^ e₀ i) / (∏ i : Fin r, q i ^ e i) := by
      rw [eq_div_iff hqe, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hm]
      rw [zpow_sub₀ (hq i), zpow_natCast, zpow_natCast, div_mul_cancel₀]
      exact pow_ne_zero _ (hq i)
    rw [hzpow, hu, map_div₀, div_mul_div_comm,
      div_eq_div_iff htau₀ (mul_ne_zero hc₀ hqe)]
    linear_combination -hkey

end

end GaloisForLFunctions.HTGeometry
