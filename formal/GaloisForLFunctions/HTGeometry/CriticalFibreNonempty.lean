import GaloisForLFunctions.HTGeometry.CriticalFibreUpperBound
import GaloisForLFunctions.HTGeometry.PowersetCardNodup

/-!
# Every critical-degree observation is realised

The fibre over an observation whose packets have exactly the critical degrees is in bijection with
the monic divisors of degree the first depth of the target `1 + U V`.  Over an algebraically closed
field that target splits into `m + n` linear factors, and any `m` of them multiply to such a
divisor, so the fibre is never empty.

No separability is needed: the existence of a compatible jet does not depend on the target having
distinct roots, only on its degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}

/-- **A split polynomial has a monic divisor of every degree up to its own.** -/
theorem exists_monic_divisor_of_natDegree_le {P : K[X]} {m : ℕ} (hm : m ≤ P.natDegree) :
    ∃ A : K[X], A.Monic ∧ A ∣ P ∧ A.natDegree = m := by
  classical
  have hcard : Multiset.card P.roots = P.natDegree :=
    ((IsAlgClosed.splits P).natDegree_eq_card_roots).symm
  have hpow : Multiset.powersetCard m P.roots ≠ 0 := by
    intro h0
    have hc := Multiset.card_powersetCard m P.roots
    rw [h0, Multiset.card_zero, hcard] at hc
    exact absurd (Nat.choose_pos hm) (by omega)
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hpow
  obtain ⟨hle, hcardt⟩ := Multiset.mem_powersetCard.1 ht
  have hmonic_all : ∀ f ∈ (t.map fun a : K => X - C a), f.Monic := by
    intro f hf
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Polynomial.monic_X_sub_C a
  refine ⟨(t.map fun a => X - C a).prod,
    Polynomial.monic_multiset_prod_of_monic t (fun a => X - C a)
      (fun a _ => Polynomial.monic_X_sub_C a), ?_, ?_⟩
  · have hsplit : P = C P.leadingCoeff * (P.roots.map fun a => X - C a).prod :=
      (IsAlgClosed.splits P).eq_prod_roots
    refine Dvd.dvd.trans ?_ (Dvd.intro_left (C P.leadingCoeff) hsplit.symm)
    exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
  · rw [Polynomial.natDegree_multiset_prod_of_monic _ hmonic_all, Multiset.map_map]
    have hone : (Multiset.map (Polynomial.natDegree ∘ fun a : K => X - C a) t)
        = Multiset.map (fun _ : K => 1) t :=
      Multiset.map_congr rfl fun a _ => Polynomial.natDegree_X_sub_C a
    rw [hone, Multiset.map_const', Multiset.sum_replicate, hcardt, smul_eq_mul, mul_one]

/-- **Every observation with packets of the critical degrees has a compatible jet.** -/
theorem nonempty_criticalFibre_criticalTails (hm : 0 < m) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) :
    Nonempty (criticalFibre K m n U V) := by
  obtain ⟨htdeg, -⟩ := degree_leadingCoeff_target_tail hm hU hV hUm hVn
  have hne : (1 + U * V) ≠ 0 := fun h => by
    rw [h, Polynomial.degree_zero] at htdeg
    exact WithBot.coe_ne_bot htdeg.symm
  have hnat : (1 + U * V).natDegree = m + n :=
    Polynomial.natDegree_eq_of_degree_eq_some htdeg
  obtain ⟨A, hmonic, hdvd, hdeg⟩ :=
    exists_monic_divisor_of_natDegree_le (P := 1 + U * V) (m := m) (by omega)
  obtain ⟨p, -⟩ := criticalTailToDivisor_surjective hm hU hV hUm hVn ⟨A, hmonic, hdvd, hdeg⟩
  exact ⟨p⟩


/-! ## The exact count for every critical-degree observation -/

/-- **The monic divisors of a prescribed degree are exactly the sub-multisets of that size of the
root multiset.** -/
theorem exists_monic_divisor_roots_eq {P : K[X]} {t : Multiset K} (hle : t ≤ P.roots) :
    ∃ A : K[X], A.Monic ∧ A ∣ P ∧ A.natDegree = Multiset.card t ∧ A.roots = t := by
  classical
  have hmonic_all : ∀ f ∈ (t.map fun a : K => X - C a), f.Monic := by
    intro f hf
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Polynomial.monic_X_sub_C a
  refine ⟨(t.map fun a => X - C a).prod,
    Polynomial.monic_multiset_prod_of_monic t (fun a => X - C a)
      (fun a _ => Polynomial.monic_X_sub_C a), ?_, ?_, ?_⟩
  · have hsplit : P = C P.leadingCoeff * (P.roots.map fun a => X - C a).prod :=
      (IsAlgClosed.splits P).eq_prod_roots
    refine Dvd.dvd.trans ?_ (Dvd.intro_left (C P.leadingCoeff) hsplit.symm)
    exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
  · rw [Polynomial.natDegree_multiset_prod_of_monic _ hmonic_all, Multiset.map_map]
    have hone : (Multiset.map (Polynomial.natDegree ∘ fun a : K => X - C a) t)
        = Multiset.map (fun _ : K => 1) t :=
      Multiset.map_congr rfl fun a _ => Polynomial.natDegree_X_sub_C a
    rw [hone, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  · exact Polynomial.roots_multiset_prod_X_sub_C t

/-- **The exact fibre count for an arbitrary critical-degree observation**: the fibre has as many
points as the target has distinct sub-multisets of roots of size the first depth.  For a separable
target these are the `choose (m+n, m)` subsets of the root set; in general repeated roots merge
them. -/
theorem nat_card_criticalFibre_eq_card_powersetCard [DecidableEq K] (hm : 0 < m) (hn : 0 < n)
    {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) :
    Nat.card (criticalFibre K m n U V)
      = (((1 + U * V).roots.powersetCard m).toFinset).card := by
  obtain ⟨htdeg, -⟩ := degree_leadingCoeff_target_tail hm hU hV hUm hVn
  have hne : (1 + U * V) ≠ 0 := fun h => by
    rw [h, Polynomial.degree_zero] at htdeg
    exact WithBot.coe_ne_bot htdeg.symm
  have hbij : Function.Bijective (criticalTailToDivisor (K := K) (n := n) hm hU hV hUm) :=
    ⟨criticalTailToDivisor_injective hm hn hU hV hUm hU0 hV0,
      criticalTailToDivisor_surjective hm hU hV hUm hVn⟩
  have hbij2 : Function.Bijective
      (fun A : {A : K[X] // A.Monic ∧ A ∣ (1 + U * V) ∧ A.natDegree = m} =>
        (⟨A.1.roots, roots_mem_powersetCard hne A.2.2.1 A.2.2.2⟩ :
          ((1 + U * V).roots.powersetCard m).toFinset)) := by
    constructor
    · exact fun A B h => monicDivisor_roots_injective (congrArg Subtype.val h)
    · rintro ⟨t, ht⟩
      obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.1 (Multiset.mem_toFinset.1 ht)
      obtain ⟨A, hmonic, hdvd, hdeg, hroots⟩ := exists_monic_divisor_roots_eq hle
      exact ⟨⟨A, hmonic, hdvd, by rw [hdeg, hcard]⟩, Subtype.ext hroots⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_of_bijective _ hbij2,
    Nat.card_eq_fintype_card, Fintype.card_coe]


/-- **The fibre count of a critical-degree observation depends only on its target.**  Two
observations whose packets have the critical degrees and whose targets `1 + U V` agree have
equinumerous fibres, whatever the packets themselves are. -/
theorem nat_card_criticalFibre_eq_of_target_eq [DecidableEq K] (hm : 0 < m) (hn : 0 < n)
    {U V U' V' : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hU' : U'.degree ≤ (m : ℕ)) (hV' : V'.degree ≤ (n : ℕ)) (hUm' : U'.coeff m ≠ 0)
    (hVn' : V'.coeff n ≠ 0) (hU0' : U'.coeff 0 = 0) (hV0' : V'.coeff 0 = 0)
    (htarget : 1 + U * V = 1 + U' * V') :
    Nat.card (criticalFibre K m n U V) = Nat.card (criticalFibre K m n U' V') := by
  rw [nat_card_criticalFibre_eq_card_powersetCard hm hn hU hV hUm hVn hU0 hV0,
    nat_card_criticalFibre_eq_card_powersetCard hm hn hU' hV' hUm' hVn' hU0' hV0', htarget]


/-- **The exact count for an observation of any packet length whose truncation has the critical
degrees.**  Only the coefficients below the horizon are seen, so an observation is counted by the
distinct sub-multisets of the truncated target's roots however long its packets are — and with no
separability. -/
theorem nat_card_criticalFibre_eq_card_powersetCard_of_truncation [DecidableEq K]
    (hm : 0 < m) (hn : 0 < n) {U V U' V' : K[X]}
    (hUU : (X : K[X]) ^ (m + n) ∣ (U - U')) (hVV : (X : K[X]) ^ (m + n) ∣ (V - V'))
    (hU : U'.degree ≤ (m : ℕ)) (hV : V'.degree ≤ (n : ℕ)) (hUm : U'.coeff m ≠ 0)
    (hVn : V'.coeff n ≠ 0) (hU0 : U'.coeff 0 = 0) (hV0 : V'.coeff 0 = 0) :
    Nat.card (criticalFibre K m n U V)
      = (((1 + U' * V').roots.powersetCard m).toFinset).card := by
  rw [Nat.card_congr (criticalFibreCongr hUU hVV)]
  exact nat_card_criticalFibre_eq_card_powersetCard hm hn hU hV hUm hVn hU0 hV0


/-- **The exactness criterion in the critical-degree regime, at every pair of depths.**  The fibre
attains the critical binomial multiplicity exactly when the target has no repeated root. -/
theorem nat_card_criticalFibre_eq_iff [DecidableEq K] (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) :
    Nat.card (criticalFibre K m n U V) = criticalHorizonMultiplicity m n ↔
      (1 + U * V).roots.Nodup := by
  obtain ⟨htdeg, -⟩ := degree_leadingCoeff_target_tail hm hU hV hUm hVn
  have hnat : (1 + U * V).natDegree = m + n :=
    Polynomial.natDegree_eq_of_degree_eq_some htdeg
  have hcardroots : Multiset.card (1 + U * V).roots = m + n := by
    rw [← (IsAlgClosed.splits (1 + U * V)).natDegree_eq_card_roots]
    exact hnat
  have hcardpow : Multiset.card ((1 + U * V).roots.powersetCard m)
      = criticalHorizonMultiplicity m n := by
    rw [Multiset.card_powersetCard, hcardroots, criticalHorizonMultiplicity]
  rw [nat_card_criticalFibre_eq_card_powersetCard hm hn hU hV hUm hVn hU0 hV0, ← hcardpow,
    Multiset.toFinset_card_eq_card_iff_nodup,
    nodup_powersetCard_iff hm (by rw [hcardroots]; omega)]


/-- **The exactness criterion in the separability phrasing.**  The critical binomial multiplicity is
attained exactly when the target is separable — so the hypothesis carried by every earlier count in
this regime is not merely sufficient but necessary. -/
theorem nat_card_criticalFibre_eq_iff_separable [DecidableEq K] (hm : 0 < m) (hn : 0 < n)
    {U V : K[X]} (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) :
    Nat.card (criticalFibre K m n U V) = criticalHorizonMultiplicity m n ↔
      (1 + U * V).Separable := by
  obtain ⟨htdeg, -⟩ := degree_leadingCoeff_target_tail hm hU hV hUm hVn
  have hne : (1 + U * V) ≠ 0 := fun h => by
    rw [h, Polynomial.degree_zero] at htdeg
    exact WithBot.coe_ne_bot htdeg.symm
  rw [nat_card_criticalFibre_eq_iff hm hn hU hV hUm hVn hU0 hV0,
    Polynomial.nodup_roots_iff_of_splits hne (IsAlgClosed.splits _)]


/-- **A degenerate target strictly loses jets.**  If the target is not separable the fibre has
strictly fewer than the critical binomial multiplicity of points. -/
theorem nat_card_criticalFibre_lt_of_not_separable [DecidableEq K] (hm : 0 < m) (hn : 0 < n)
    {U V : K[X]} (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hsep : ¬ (1 + U * V).Separable) :
    Nat.card (criticalFibre K m n U V) < criticalHorizonMultiplicity m n := by
  have hle := nat_card_criticalFibre_le hm hn hU hV hUm hVn hU0 hV0
  have hne : Nat.card (criticalFibre K m n U V) ≠ criticalHorizonMultiplicity m n := fun h =>
    hsep ((nat_card_criticalFibre_eq_iff_separable hm hn hU hV hUm hVn hU0 hV0).1 h)
  omega

end GaloisForLFunctions.HTGeometry
