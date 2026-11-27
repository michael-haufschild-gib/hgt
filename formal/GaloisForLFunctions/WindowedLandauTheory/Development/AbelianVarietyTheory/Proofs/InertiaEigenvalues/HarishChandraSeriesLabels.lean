import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalLabelUniqueness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalInductionGenericConstituents
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSupportPermutation

/-! The polynomial of a Harish–Chandra series factors according to its
cuspidal support. A squarefree polynomial has a single irreducible product. -/

noncomputable section
open GaloisForLFunctions Polynomial
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private abbrev LabelledCuspidal (g : ℕ) := (ZMod g)[X] × Pc g

private theorem ip_eq_pairing {G : Type} [Group G] [Fintype G] (α β : G → ℂ) :
    ip α β = characterPairing G α β := by
  rw [characterPairing_comm G α β, ip, characterPairing, Nat.card_eq_fintype_card]

private theorem label_product_properties (L : LabelDatum g) (Q : List (LabelledCuspidal g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) :
    (Q.map Prod.fst).prod.Monic ∧ (Q.map Prod.fst).prod.natDegree = degL (Q.map Prod.snd) ∧
      (Q.map Prod.fst).prod.coeff 0 ≠ 0 := by
  induction Q with
  | nil => simp [degL]
  | cons p Q ih =>
    obtain ⟨hm, _, h0, hd⟩ := (hQ p List.mem_cons_self).1
    obtain ⟨hm', hd', h0'⟩ := ih (fun q hq => hQ q (List.mem_cons_of_mem p hq))
    simp only [List.map_cons, List.prod_cons]
    refine ⟨hm.mul hm', ?_, ?_⟩
    · rw [hm.natDegree_mul hm', hd, hd']
      rfl
    · rw [Polynomial.mul_coeff_zero]
      exact mul_ne_zero h0 h0'

private theorem factors_of_label_product (L : LabelDatum g) (Q : List (LabelledCuspidal g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) :
    ((Q.map Prod.fst : List (ZMod g)[X]) : Multiset _) =
      UniqueFactorizationMonoid.normalizedFactors (Q.map Prod.fst).prod := by
  have hI (P : (ZMod g)[X]) (hP : P ∈ ((Q.map Prod.fst : List (ZMod g)[X]) : Multiset _)) :
      Irreducible P ∧ P.Monic := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hP)
    exact ⟨(hQ q hq).1.2.1, (hQ q hq).1.1⟩
  rw [← Multiset.prod_coe,
    UniqueFactorizationMonoid.normalizedFactors_prod_eq _ (fun P hP => (hI P hP).1)]
  exact (Multiset.map_id _).symm.trans
    (Multiset.map_congr rfl fun P hP => ((hI P hP).2.normalize_eq_self).symm)

private theorem cuspidals_of_labelled (L : LabelDatum g) (Q : List (LabelledCuspidal g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (hQ q hq).2.1

/-- The polynomial of a labelled series is monic, of the ambient degree, and has nonzero constant term. -/
theorem hasLabel_polynomial_properties (L : LabelDatum g) {χ : Gn g n → ℂ}
    {f : (ZMod g)[X]} (hf : HasLabel L χ f) :
    f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
  obtain ⟨Q, hQ, hdeg, rfl, -⟩ := hf
  obtain ⟨hm, hd, h0⟩ := label_product_properties L Q hQ
  exact ⟨hm, hd.trans hdeg, h0⟩

private def cuspidalLabel (L : LabelDatum g) (p : Pc g) : (ZMod g)[X] :=
  if h : ∃ P, IsCuspOf L P p.2 then h.choose else 0

private theorem cuspidalLabel_eq (L : LabelDatum g) (hg : 5 ≤ g)
    (p : Pc g) (P : (ZMod g)[X]) (hP : IsCuspOf L P p.2) : cuspidalLabel L p = P := by
  have hex : ∃ R, IsCuspOf L R p.2 := ⟨P, hP⟩
  rw [cuspidalLabel, dif_pos hex]
  exact isCuspOf_label_eq L hg hex.choose_spec hP

private def genuine_of_isChar {G : Type} [Group G] (α : G → ℂ) (hα : IsChar α) :
    GenuineCharacter G := ⟨α, by
      obtain ⟨V, hV⟩ := hα
      exact AddSubmonoid.subset_closure ⟨V, funext hV⟩⟩

/-- An irreducible character belongs to at most one polynomial Harish–Chandra series. -/
theorem hasLabel_unique (L : LabelDatum g) (hg : 5 ≤ g) {χ : Gn g n → ℂ} (hχ : IsIrr χ)
    {f f' : (ZMod g)[X]} (hf : HasLabel L χ f) (hf' : HasLabel L χ f') : f = f' := by
  obtain ⟨Q, hQ, hdQ, rfl, hχQ⟩ := hf
  obtain ⟨R, hR, hdR, rfl, hχR⟩ := hf'
  let C := Q.map Prod.snd
  let D := R.map Prod.snd
  have hC := cuspidals_of_labelled L Q hQ
  have hD := cuspidals_of_labelled L R hR
  let α := genuine_of_isChar (hcL C n) (by
    rw [← hdQ]
    exact isChar_hcL C fun p hp => isChar_of_cuspidal (hC p hp))
  let β := genuine_of_isChar (hcL D n) (by
    rw [← hdR]
    exact isChar_hcL D fun p hp => isChar_of_cuspidal (hD p hp))
  obtain ⟨V, hV, hχV⟩ := hχ
  have hχ' : χ ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨V, hV, funext hχV⟩
  have hα : characterPairing (Gn g n) α.val χ ≠ 0 := by
    change characterPairing (Gn g n) (hcL C n) χ ≠ 0
    rw [characterPairing_comm, ← ip_eq_pairing]
    exact hχQ
  have hβ : characterPairing (Gn g n) β.val χ ≠ 0 := by
    change characterPairing (Gn g n) (hcL D n) χ ≠ 0
    rw [characterPairing_comm, ← ip_eq_pairing]
    exact hχR
  have hnonzero : characterPairing (Gn g n) (hcL C n) (hcL D n) ≠ 0 :=
    CuspGL.pairing_ne_zero_of_common_simple α β hχ' hα hβ
  have hperm : C.Perm D := Multiset.coe_eq_coe.mp (by
    by_contra hne
    exact hnonzero (characterPairing_hcL_eq_zero_of_multiset_ne C D hdQ hdR hC hD hne))
  have hlabels (T : List (LabelledCuspidal g)) (hT : ∀ p ∈ T, IsCuspOf L p.1 p.2.2) :
      T.map Prod.fst = (T.map Prod.snd).map (cuspidalLabel L) := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => (cuspidalLabel_eq L hg p.2 p.1 (hT p hp)).symm
  rw [hlabels Q hQ, hlabels R hR]
  exact (hperm.map (cuspidalLabel L)).prod_eq

private theorem normalized_factor_isPrimeLab {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0)
    {P : (ZMod g)[X]} (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors f) :
    IsPrimeLab P.natDegree P := by
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  have hmon : P.Monic := by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor P hP]
    exact monic_normalize hirr.ne_zero
  refine ⟨hmon, hirr, ?_, rfl⟩
  intro h
  exact h0 (X_dvd_iff.mp ((X_dvd_iff.mpr h).trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)))

private theorem exists_cuspidal_section (L : LabelDatum g) :
    ∃ t : (P : (ZMod g)[X]) → Gn g P.natDegree → ℂ,
      ∀ P, IsPrimeLab P.natDegree P →
        IsCuspOf L P (t P) ∧
          t P 1 = ∏ i ∈ Finset.Ico 1 P.natDegree, ((g : ℂ) ^ i - 1) := by
  refine ⟨fun P => if h : 0 < P.natDegree then (GlobalTheory.green g L _ h).choose P else 0, ?_⟩
  intro P hP
  have hd : 0 < P.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hP.2.1)
  simp only [dif_pos hd]
  exact (GlobalTheory.green g L _ hd).choose_spec.1 P hP

private theorem label_factors (L : LabelDatum g) (f : (ZMod g)[X])
    (hm : f.Monic) (hd : f.natDegree = n) (h0 : f.coeff 0 ≠ 0)
    (t : (P : (ZMod g)[X]) → Gn g P.natDegree → ℂ)
    (ht : ∀ P, IsPrimeLab P.natDegree P → IsCuspOf L P (t P) ∧
      t P 1 = ∏ i ∈ Finset.Ico 1 P.natDegree, ((g : ℂ) ^ i - 1)) :
    let Q : List (LabelledCuspidal g) := (UniqueFactorizationMonoid.normalizedFactors f).toList.map
      fun P => (P, ⟨P.natDegree, t P⟩)
    (∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) ∧
      Q.map Prod.fst = (UniqueFactorizationMonoid.normalizedFactors f).toList ∧
      degL (Q.map Prod.snd) = n ∧ (Q.map Prod.fst).prod = f := by
  dsimp only
  let F := UniqueFactorizationMonoid.normalizedFactors f
  let Q : List (LabelledCuspidal g) := F.toList.map fun P => (P, ⟨P.natDegree, t P⟩)
  change (∀ p ∈ Q, _) ∧ Q.map Prod.fst = F.toList ∧ degL (Q.map Prod.snd) = n ∧ _
  have hQ (p : LabelledCuspidal g) (hp : p ∈ Q) :
      IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1) := by
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hp
    exact ht P (normalized_factor_isPrimeLab h0 (Multiset.mem_toList.mp hP))
  have hfst : Q.map Prod.fst = F.toList := by simp [Q, List.map_map, Function.comp_def]
  obtain ⟨hQm, hQd, -⟩ := label_product_properties L Q fun p hp => (hQ p hp).1
  have hp : (Q.map Prod.fst).prod = f := by
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hm.ne_zero
    change Associated F.prod f at hassoc
    rw [← Multiset.coe_toList F, ← hfst, Multiset.prod_coe] at hassoc
    exact eq_of_monic_of_associated hQm hm hassoc
  exact ⟨hQ, hfst, hQd.symm.trans ((congrArg natDegree hp).trans hd), hp⟩

/-- Every monic polynomial with nonzero constant term labels a generic
irreducible constituent of the product of its cuspidal factors. -/
theorem exists_generic_of_polynomial_label (L : LabelDatum g) (f : (ZMod g)[X])
    (hm : f.Monic) (hd : f.natDegree = n) (h0 : f.coeff 0 ≠ 0) :
    ∃ χ : Gn g n → ℂ, IsIrr χ ∧ HasLabel L χ f ∧ wh ZMod.stdAddChar χ ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_cuspidal_section L
  let Q : List (LabelledCuspidal g) := (UniqueFactorizationMonoid.normalizedFactors f).toList.map
    fun P => (P, ⟨P.natDegree, t P⟩)
  obtain ⟨hQ, _, hQdeg, hp⟩ := label_factors L f hm hd h0 t ht
  have hlabel (p : LabelledCuspidal g) (hp : p ∈ Q) : IsCuspOf L p.1 p.2.2 := (hQ p hp).1
  have hex : ∃ χ : Gn g n → ℂ, IsIrr χ ∧ wh ZMod.stdAddChar χ ≠ 0 ∧ ip (hcL (Q.map Prod.snd) n) χ ≠ 0 := by
    rw [← hQdeg]
    exact exists_generic_constituent_hcL _ (cuspidals_of_labelled L Q hlabel)
  obtain ⟨χ, hχ, hw, hip⟩ := hex
  refine ⟨χ, hχ, ⟨Q, hlabel, hQdeg, hp.symm, ?_⟩, hw⟩
  rw [ip_eq_pairing, characterPairing_comm, ← ip_eq_pairing]
  exact hip

/-- A squarefree label gives a single irreducible character, obtained by
parabolic induction of the cuspidals attached to its irreducible factors. -/
theorem squarefree_label_series (L : LabelDatum g) (hg : 5 ≤ g) (f : (ZMod g)[X])
    (hm : f.Monic) (hd : f.natDegree = n) (h0 : f.coeff 0 ≠ 0) (hs : Squarefree f) :
    ∃ Q : List ((ZMod g)[X] × Pc g),
      (∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) ∧
      ((Q.map Prod.fst : List (ZMod g)[X]) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f ∧
      degL (Q.map Prod.snd) = n ∧
      {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = {hcL (Q.map Prod.snd) n} := by
  obtain ⟨t, ht⟩ := exists_cuspidal_section L
  let s (P : (ZMod g)[X]) : Pc g := ⟨P.natDegree, t P⟩
  let F := UniqueFactorizationMonoid.normalizedFactors f
  let Q := F.toList.map fun P => (P, s P)
  obtain ⟨hQ, hfst, hQdeg, hp⟩ := label_factors L f hm hd h0 t ht
  have hsnd : Q.map Prod.snd = F.toList.map s := by simp [Q, List.map_map, Function.comp_def]
  have hQ' (p : LabelledCuspidal g) (hp : p ∈ Q) : IsCuspOf L p.1 p.2.2 := (hQ p hp).1
  have hQc := cuspidals_of_labelled L Q hQ'
  have heq : ((Q.map Prod.fst : List (ZMod g)[X]) : Multiset _) = F := by
    rw [hfst, Multiset.coe_toList]
  have hFnd : F.toList.Nodup := Multiset.coe_nodup.mp (by
    rw [Multiset.coe_toList]
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hm.ne_zero).mp hs)
  have hsInj (P Q : (ZMod g)[X]) (hP : P ∈ F.toList) (hQ : Q ∈ F.toList) (he : s P = s Q) : P = Q := by
    have hp' : IsCuspOf L P (s P).2 := (ht P (normalized_factor_isPrimeLab h0 (Multiset.mem_toList.mp hP))).1
    have hq' : IsCuspOf L Q (s Q).2 := (ht Q (normalized_factor_isPrimeLab h0 (Multiset.mem_toList.mp hQ))).1
    rw [← he] at hq'
    exact isCuspOf_label_eq L hg hp' hq'
  have hN : (Q.map Prod.snd).Nodup := by
    rw [hsnd]
    exact List.Nodup.map_on (fun P hP Q hQ he => hsInj P Q hP hQ he) hFnd
  have hirr := isIrr_hcL_of_nodup (Q.map Prod.snd) hQdeg hQc hN
  refine ⟨Q, fun p hp => hQ p hp, heq, hQdeg, ?_⟩
  ext χ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hχ, R, hR, hdR, hfR, hip⟩
    have hr (p : LabelledCuspidal g) (hp : p ∈ R) : p.2 = s p.1 := by
      obtain ⟨P, ⟨d, ξ⟩⟩ := p
      have hξ : IsCuspOf L P ξ := hR _ hp
      have hdp : P.natDegree = d := hξ.1.2.2.2
      subst d
      have hte := (ht P hξ.1).1
      have h := isCuspOf_character_eq L hg hξ hte
      change (⟨P.natDegree, ξ⟩ : Pc g) = ⟨P.natDegree, t P⟩
      rw [h]
    have hsR : R.map Prod.snd = (R.map Prod.fst).map s := by
      rw [List.map_map]
      exact List.map_congr_left hr
    have hperm : (R.map Prod.fst).Perm F.toList := Multiset.coe_eq_coe.mp (by
      rw [Multiset.coe_toList, factors_of_label_product L R hR, ← hfR])
    have hperm' : (R.map Prod.snd).Perm (Q.map Prod.snd) := by
      rw [hsR, hsnd]
      exact hperm.map s
    rw [hcL_eq_of_perm_cuspidal_nodup (R.map Prod.snd) (Q.map Prod.snd) hdR hQdeg hperm'
      (hperm'.nodup_iff.mpr hN) hN (cuspidals_of_labelled L R hR) hQc, ip_eq_pairing] at hip
    obtain ⟨V, hV, hχV⟩ := hχ
    obtain ⟨W, hW, hχW⟩ := hirr
    have hV' : χ ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨V, hV, funext hχV⟩
    have hW' : hcL (Q.map Prod.snd) n ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨W, hW, funext hχW⟩
    by_contra hn
    exact hip ((CuspGL.pairing_simple hV' hW').trans (if_neg hn))
  · rintro rfl
    refine ⟨hirr, Q, hQ', hQdeg, hp.symm, ?_⟩
    rw [ip_eq_pairing, characterPairing_hcL_self_eq_one_of_nodup _ hQdeg hQc hN]
    exact one_ne_zero

end GlobalTheory.GLq
