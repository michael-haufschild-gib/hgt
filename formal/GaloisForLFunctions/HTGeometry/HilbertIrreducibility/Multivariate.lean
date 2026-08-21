import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Kronecker
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Main
import GaloisForLFunctions.HTGeometry.PrimeSubsetFactor
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Hilbert irreducibility in several variables

Kronecker substitution reduces the specialization of one variable of a multivariate irreducible
polynomial to the two-variable case: a factorization of the specialized polynomial is transported,
through the degree-bounded bijection `kron`, to a factorization of the original one.
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial MvPolynomial

/-- A nonzero polynomial over `ℚ[X]` is a constant in `Y` times a finite family of irreducible
factors of positive `Y`-degree. -/
theorem exists_factorisation {P : Polynomial (Polynomial ℚ)} (hP : P ≠ 0) :
    ∃ (n : ℕ) (g₀ : Polynomial ℚ) (g : Fin n → Polynomial (Polynomial ℚ)),
      g₀ ≠ 0 ∧ (∀ i, Irreducible (g i)) ∧ (∀ i, 1 ≤ (g i).natDegree) ∧
      P = Polynomial.C g₀ * ∏ i, g i := by
  classical
  set L := UniqueFactorizationMonoid.factors P with hL
  have hirr : ∀ q ∈ L, Irreducible q := fun q hq =>
    UniqueFactorizationMonoid.irreducible_of_factor q hq
  set L1 : Multiset (Polynomial (Polynomial ℚ)) := L.filter (fun q => 1 ≤ q.natDegree) with hL1
  set L0 : Multiset (Polynomial (Polynomial ℚ)) := L.filter (fun q => ¬ (1 ≤ q.natDegree)) with hL0
  have hsplit : L1 + L0 = L := Multiset.filter_add_not _ L
  have hprodL : L0.prod * L1.prod = L.prod := by
    rw [← hsplit, Multiset.prod_add, mul_comm]
  have h0ne : (0 : Polynomial (Polynomial ℚ)) ∉ L0 := fun h0 =>
    (hirr 0 (Multiset.mem_of_mem_filter h0)).ne_zero rfl
  have hdeg0 : L0.prod.natDegree = 0 := by
    rw [Polynomial.natDegree_multiset_prod L0 h0ne]
    refine Multiset.sum_eq_zero ?_
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
    have := (Multiset.mem_filter.mp hq).2
    omega
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hdeg0
  have hL0ne : L0.prod ≠ 0 := Multiset.prod_ne_zero h0ne
  have hane : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact hL0ne ha.symm
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hP
  obtain ⟨r, hr, hrC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hrne : r ≠ 0 := hr.ne_zero
  have hlist : L1.prod = ∏ i : Fin L1.toList.length, L1.toList.get i := by
    rw [← Multiset.prod_toList]
    conv_lhs => rw [← List.ofFn_get L1.toList]
    rw [List.prod_ofFn]
  refine ⟨L1.toList.length, a * r, fun i => L1.toList.get i, mul_ne_zero hane hrne, ?_, ?_, ?_⟩
  · intro i
    exact hirr _ (Multiset.mem_of_mem_filter (Multiset.mem_toList.mp (List.get_mem _ i)))
  · intro i
    exact (Multiset.mem_filter.mp (Multiset.mem_toList.mp (List.get_mem _ i))).2
  · rw [← hlist, map_mul, ← hu, ← hprodL, ← ha, hrC]
    ring

/-- Away from the roots of a suitable nonzero polynomial, boundedness of a specialization forces
boundedness of the polynomial itself. -/
theorem exists_exclusion {k : ℕ} (d : ℕ) (w : MvPolynomial (Fin k) (Polynomial ℚ)) :
    ∃ e : Polynomial ℚ, e ≠ 0 ∧ ∀ b : ℚ, Polynomial.eval b e ≠ 0 →
      KBounded d (MvPolynomial.map (Polynomial.evalRingHom b) w) → KBounded d w := by
  classical
  by_cases hw : KBounded d w
  · exact ⟨1, one_ne_zero, fun _ _ _ => hw⟩
  · have hex : ∃ a ∈ w.support, ∃ j : Fin k, d ≤ a j := by
      by_contra hc
      apply hw
      intro a ha j
      by_contra hlt
      exact hc ⟨a, ha, j, by omega⟩
    obtain ⟨a, ha, j, hj⟩ := hex
    refine ⟨w.coeff a, MvPolynomial.mem_support_iff.mp ha, fun b hb hbnd => ?_⟩
    exfalso
    have hmem : a ∈ (MvPolynomial.map (Polynomial.evalRingHom b) w).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
      exact hb
    have := hbnd a hmem j
    omega

/-- **One-variable specialization of a multivariate irreducible polynomial.**  Kronecker
substitution transports a factorization of the specialization back to a factorization of the
original polynomial, so all but finitely many of the values supplied by the one-parameter theorem
for the irreducible factors of `S_d f` keep irreducibility. -/
theorem exists_infinite_specialisation {k : ℕ}
    {f : MvPolynomial (Fin k) (Polynomial ℚ)} (hf : Irreducible f) (hdeg : 0 < f.totalDegree) :
    {b : ℚ | Irreducible (MvPolynomial.map (Polynomial.evalRingHom b) f)}.Infinite := by
  classical
  obtain ⟨d, hd1, hfB⟩ : ∃ d : ℕ, 1 ≤ d ∧ KBounded d f := by
    refine ⟨(Finset.univ.sup fun j : Fin k => MvPolynomial.degreeOf j f) + 1, by omega, ?_⟩
    refine kBounded_of_degreeOf fun j => ?_
    have hle := Finset.le_sup (f := fun j : Fin k => MvPolynomial.degreeOf j f) (Finset.mem_univ j)
    omega
  have hd0 : 0 < d := hd1
  have hdk : 0 < d ^ k := pow_pos hd0 k
  have hfne : f ≠ 0 := hf.ne_zero
  have hPne : kron (Polynomial ℚ) d k f ≠ 0 := kron_ne_zero hd1 hfB hfne
  obtain ⟨n, g₀, g, hg₀, hgirr, hgdeg, hPeq⟩ := exists_factorisation hPne
  have hgne : ∀ i, g i ≠ 0 := fun i => (hgirr i).ne_zero
  have hnatP : (kron (Polynomial ℚ) d k f).natDegree < d ^ k := natDegree_kron_lt hdk hfB
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      subst hn
      have hPc : kron (Polynomial ℚ) d k f = Polynomial.C g₀ := by rw [hPeq]; simp
      have hfeq : f = MvPolynomial.C g₀ :=
        kron_injOn hd1 hfB (kBounded_C hd0 g₀) (by rw [hPc, kron_C])
      rw [hfeq, MvPolynomial.totalDegree_C] at hdeg
      omega
    · exact hn
  have hUV : ∀ t : Finset (Fin n), ∃ u v : MvPolynomial (Fin k) (Polynomial ℚ),
      KBounded d u ∧ KBounded d v ∧
        kron (Polynomial ℚ) d k u = ∏ i ∈ t, g i ∧
        kron (Polynomial ℚ) d k v = ∏ i ∈ tᶜ, g i := by
    intro t
    have hsplit : (∏ i ∈ t, g i) * ∏ i ∈ tᶜ, g i = ∏ i, g i := Finset.prod_mul_prod_compl t g
    have hdvdU : (∏ i ∈ t, g i) ∣ kron (Polynomial ℚ) d k f :=
      ⟨Polynomial.C g₀ * ∏ i ∈ tᶜ, g i, by rw [hPeq, ← hsplit]; ring⟩
    have hdvdV : (∏ i ∈ tᶜ, g i) ∣ kron (Polynomial ℚ) d k f :=
      ⟨Polynomial.C g₀ * ∏ i ∈ t, g i, by rw [hPeq, ← hsplit]; ring⟩
    obtain ⟨u, huB, hku⟩ := exists_kron_eq (k := k) hd1 (P := ∏ i ∈ t, g i) fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvdU hPne) (lt_of_lt_of_le hnatP hm))
    obtain ⟨v, hvB, hkv⟩ := exists_kron_eq (k := k) hd1 (P := ∏ i ∈ tᶜ, g i) fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvdV hPne) (lt_of_lt_of_le hnatP hm))
    exact ⟨u, v, huB, hvB, hku, hkv⟩
  choose ut vt hutB hvtB hkut hkvt using hUV
  have hexcl := fun t : Finset (Fin n) =>
    exists_exclusion d (MvPolynomial.C g₀ * ut t * vt t)
  choose e he0 he using hexcl
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin k →₀ ℕ, f.coeff a₀ ≠ 0 := by
    by_contra hc
    refine hfne (MvPolynomial.ext f 0 fun m => ?_)
    rw [MvPolynomial.coeff_zero]
    exact not_not.mp (fun h => hc ⟨m, h⟩)
  have hEne : ((∏ t : Finset (Fin n), e t) * g₀) * f.coeff a₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ => he0 t) hg₀) ha₀
  have hHIT := hilbert_irreducibility_family g hgirr hgdeg
  have hfin : {x : ℚ | (((∏ t : Finset (Fin n), e t) * g₀) * f.coeff a₀).IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot hEne
  refine Set.Infinite.mono ?_ (hHIT.sdiff hfin)
  rintro b ⟨hbHIT, hbE⟩
  have hEval : Polynomial.eval b (((∏ t : Finset (Fin n), e t) * g₀) * f.coeff a₀) ≠ 0 := hbE
  rw [Polynomial.eval_mul, Polynomial.eval_mul, mul_ne_zero_iff, mul_ne_zero_iff] at hEval
  obtain ⟨⟨hEprod, hγ⟩, hcoeff0⟩ := hEval
  have het : ∀ t : Finset (Fin n), Polynomial.eval b (e t) ≠ 0 := by
    rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff] at hEprod
    exact fun t => hEprod t (Finset.mem_univ t)
  set q : Fin n → Polynomial ℚ :=
    fun i => Polynomial.map (Polynomial.evalRingHom b) (g i) with hq_def
  have hqirr : ∀ i, Irreducible (q i) := by
    intro i; simp only [hq_def]; exact hbHIT i
  have hqne : ∀ i, q i ≠ 0 := fun i => (hqirr i).ne_zero
  have hq1 : ∀ i, 1 ≤ (q i).natDegree := by
    intro i
    by_contra hc
    have h0 : (q i).natDegree = 0 := by omega
    obtain ⟨c, hc'⟩ := Polynomial.natDegree_eq_zero.mp h0
    refine (hqirr i).not_isUnit ?_
    rw [← hc']
    refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
    intro hc0
    rw [hc0, map_zero] at hc'
    exact hqne i hc'.symm
  set fb : MvPolynomial (Fin k) ℚ := MvPolynomial.map (Polynomial.evalRingHom b) f with hfb_def
  have hfbB : KBounded d fb := by rw [hfb_def]; exact kBounded_map _ hfB
  have hkfb : kron ℚ d k fb = Polynomial.C (Polynomial.eval b g₀) * ∏ i, q i := by
    rw [hfb_def, ← kron_map, hPeq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    simp only [hq_def, Polynomial.coe_evalRingHom]
  have hfbne : fb ≠ 0 := by
    intro h0
    apply hcoeff0
    have hcz := congrArg (fun p => MvPolynomial.coeff a₀ p) h0
    simp only [hfb_def, MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
      Polynomial.coe_evalRingHom] at hcz
    exact hcz
  have hnu : ¬ IsUnit fb := by
    intro hcu
    have h1 : IsUnit (kron ℚ d k fb) := hcu.map (kron ℚ d k)
    rw [hkfb] at h1
    have h2 := Polynomial.natDegree_eq_zero_of_isUnit h1
    rw [Polynomial.natDegree_C_mul hγ, Polynomial.natDegree_prod _ _ (fun i _ => hqne i)] at h2
    obtain ⟨i0⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn1
    have h3 : 1 ≤ ∑ i, (q i).natDegree :=
      le_trans (hq1 i0) (Finset.single_le_sum (f := fun i => (q i).natDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i0))
    omega
  refine ⟨hnu, fun u v huv => ?_⟩
  by_contra hcon
  have hu : ¬ IsUnit u := fun h => hcon (Or.inl h)
  have hv : ¬ IsUnit v := fun h => hcon (Or.inr h)
  have hune : u ≠ 0 := by rintro rfl; rw [zero_mul] at huv; exact hfbne huv
  have hvne : v ≠ 0 := by rintro rfl; rw [mul_zero] at huv; exact hfbne huv
  have huvB : KBounded d (u * v) := huv ▸ hfbB
  have huB : KBounded d u := kBounded_of_mul_left hd0 hune hvne huvB
  have hvB : KBounded d v := kBounded_of_mul_right hd0 hune hvne huvB
  have hmul : kron ℚ d k u * kron ℚ d k v = Polynomial.C (Polynomial.eval b g₀) * ∏ i, q i := by
    rw [← map_mul, ← huv, hkfb]
  have hCinv : Polynomial.C (Polynomial.eval b g₀)⁻¹ * Polynomial.C (Polynomial.eval b g₀)
      = (1 : Polynomial ℚ) := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hγ, Polynomial.C_1]
  have hprod : (kron ℚ d k u * Polynomial.C (Polynomial.eval b g₀)⁻¹) * kron ℚ d k v
      = ∏ i, q i := by
    calc (kron ℚ d k u * Polynomial.C (Polynomial.eval b g₀)⁻¹) * kron ℚ d k v
        = Polynomial.C (Polynomial.eval b g₀)⁻¹ * (kron ℚ d k u * kron ℚ d k v) := by ring
      _ = Polynomial.C (Polynomial.eval b g₀)⁻¹ *
            (Polynomial.C (Polynomial.eval b g₀) * ∏ i, q i) := by rw [hmul]
      _ = (Polynomial.C (Polynomial.eval b g₀)⁻¹ * Polynomial.C (Polynomial.eval b g₀)) *
            ∏ i, q i := by ring
      _ = ∏ i, q i := by rw [hCinv, one_mul]
  have hqprime : ∀ i ∈ (Finset.univ : Finset (Fin n)), Prime (q i) := fun i _ =>
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (hqirr i)
  obtain ⟨t, -, hassoc0⟩ :=
    PrimeSubsetFactor.exists_subset_associated Finset.univ q hqprime _ _ hprod
  have hCunit : IsUnit (Polynomial.C (Polynomial.eval b g₀)⁻¹ : Polynomial ℚ) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hγ))
  have hassocU : Associated (kron ℚ d k u) (∏ i ∈ t, q i) :=
    Associated.trans ⟨hCunit.unit, by rw [hCunit.unit_spec]⟩ hassoc0
  have hassocV : Associated (kron ℚ d k v) (∏ i ∈ tᶜ, q i) := by
    rw [Finset.compl_eq_univ_sdiff]
    exact PrimeSubsetFactor.associated_sdiff_of_associated (Finset.subset_univ t) hqprime
      hprod hassoc0
  have hmapU : kron ℚ d k (MvPolynomial.map (Polynomial.evalRingHom b) (ut t))
      = ∏ i ∈ t, q i := by
    rw [← kron_map, hkut, Polynomial.map_prod]
  have hmapV : kron ℚ d k (MvPolynomial.map (Polynomial.evalRingHom b) (vt t))
      = ∏ i ∈ tᶜ, q i := by
    rw [← kron_map, hkvt, Polynomial.map_prod]
  obtain ⟨cu, hcu⟩ := hassocU
  obtain ⟨ru, hru, hruC⟩ := Polynomial.isUnit_iff.mp cu.isUnit
  obtain ⟨cv, hcv⟩ := hassocV
  obtain ⟨rv, hrv, hrvC⟩ := Polynomial.isUnit_iff.mp cv.isUnit
  have hIdU : u * MvPolynomial.C ru = MvPolynomial.map (Polynomial.evalRingHom b) (ut t) := by
    refine kron_injOn hd1 (kBounded_mul_C ru huB) (kBounded_map _ (hutB t)) ?_
    rw [map_mul, kron_C, hmapU, hruC]
    exact hcu
  have hIdV : v * MvPolynomial.C rv = MvPolynomial.map (Polynomial.evalRingHom b) (vt t) := by
    refine kron_injOn hd1 (kBounded_mul_C rv hvB) (kBounded_map _ (hvtB t)) ?_
    rw [map_mul, kron_C, hmapV, hrvC]
    exact hcv
  have hnuU : ¬ IsUnit (ut t) := by
    intro hU
    have h1 : IsUnit (u * MvPolynomial.C ru) := by
      rw [hIdU]
      exact hU.map (MvPolynomial.map (Polynomial.evalRingHom b))
    exact hu (isUnit_of_mul_isUnit_left h1)
  have hnuV : ¬ IsUnit (vt t) := by
    intro hV
    have h1 : IsUnit (v * MvPolynomial.C rv) := by
      rw [hIdV]
      exact hV.map (MvPolynomial.map (Polynomial.evalRingHom b))
    exact hv (isUnit_of_mul_isUnit_left h1)
  have hkw : kron (Polynomial ℚ) d k (MvPolynomial.C g₀ * ut t * vt t)
      = kron (Polynomial ℚ) d k f := by
    rw [map_mul, map_mul, kron_C, hkut, hkvt, hPeq, ← Finset.prod_mul_prod_compl t g, mul_assoc]
  by_cases hwB : KBounded d (MvPolynomial.C g₀ * ut t * vt t)
  · have hfeq : MvPolynomial.C g₀ * ut t * vt t = f := kron_injOn hd1 hwB hfB hkw
    rcases hf.isUnit_or_isUnit hfeq.symm with h | h
    · exact hnuU (isUnit_of_mul_isUnit_right h)
    · exact hnuV h
  · apply hwB
    refine he t b (het t) ?_
    have hmapw : MvPolynomial.map (Polynomial.evalRingHom b) (MvPolynomial.C g₀ * ut t * vt t)
        = (u * v) * MvPolynomial.C (Polynomial.eval b g₀ * ru * rv) := by
      rw [map_mul, map_mul, MvPolynomial.map_C, ← hIdU, ← hIdV, map_mul, map_mul]
      simp only [Polynomial.coe_evalRingHom]
      ring
    rw [hmapw, ← huv]
    exact kBounded_mul_C _ hfbB

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility

