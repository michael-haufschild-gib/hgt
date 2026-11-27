import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.StatementT
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenLabelRoots

/-! The roots of a squarefree polynomial are indexed by Frobenius cycles.
Frobenius-invariant subsets give monic divisors over the prime field. -/

noncomputable section

open Polynomial

namespace WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder

section PrimeTo

variable {M : Type*} [Monoid M]

lemma primeToPart_pow (ℓ : ℕ) (x : M) (k : ℕ) (h : orderOf (x ^ k) = orderOf x) :
    primeToPart ℓ (x ^ k) = primeToPart ℓ x ^ k := by
  unfold primeToPart
  rw [h, ← pow_mul, ← pow_mul, mul_comm k]

lemma primeToPart_coprime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    (orderOf (primeToPart ℓ x)).Coprime ℓ := by
  have hn0 : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  have hm : orderOf x = ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ) :=
    (Nat.ordProj_mul_ordCompl_eq_self (orderOf x) ℓ).symm
  have key : ∀ u : ℕ, (x ^ (ℓ ^ (orderOf x).factorization ℓ * u)) ^
      (orderOf x / ℓ ^ (orderOf x).factorization ℓ) = 1 := fun u => by
    rw [← pow_mul, show ℓ ^ (orderOf x).factorization ℓ * u * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)
      = (ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) * u by ring,
      ← hm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hdvd : orderOf (primeToPart ℓ x) ∣ orderOf x / ℓ ^ (orderOf x).factorization ℓ :=
    orderOf_dvd_of_pow_eq_one (key _)
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_ordCompl hℓ hn0).symm

lemma primeToPart_isOfFinOrder (ℓ : ℕ) (x : M) (hx : IsOfFinOrder x) :
    IsOfFinOrder (primeToPart ℓ x) := hx.pow

end PrimeTo

private theorem mem_range_of_pow_eq {g : ℕ} [Fact g.Prime] (x : Fbar g) (hx : x ^ g = x) :
    x ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := by
  obtain ⟨m, hm⟩ := (mem_bot_iff_intCast g (Fbar g)).mp ((Subfield.mem_bot_iff_pow_eq_self (Fbar g) g).mpr hx)
  exact ⟨(m : ZMod g), by simpa using hm⟩

/-- A Frobenius-stable multiset, with multiplicities, is the root multiset
of a unique monic polynomial over the prime field. -/
theorem existsUnique_monic_of_frobenius_stable {g : ℕ} [Fact g.Prime] (S : Multiset (Fbar g))
    (hS : S.map (fun x => x ^ g) = S) :
    ∃! q : (ZMod g)[X], q.Monic ∧ rootsBar q = S := by
  let j := algebraMap (ZMod g) (Fbar g)
  let Q : (Fbar g)[X] := (S.map fun x => X - C x).prod
  have hQm : Q.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
  have hfix : Q.map (frobenius (Fbar g) g) = Q := by
    rw [show Q = (S.map fun x => X - C x).prod from rfl, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [← hS, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp [frobenius_def]
  have hcoeff : Q ∈ lifts j := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply mem_range_of_pow_eq
    have h := congrArg (fun p => p.coeff n) hfix
    simpa only [coeff_map, frobenius_def] using h
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hcoeff hQm
  have hroots : rootsBar q = S := by
    change (q.map j).roots = S
    rw [hq, show Q = _ from rfl, roots_multiset_prod_X_sub_C]
  refine ⟨q, ⟨hqm, hroots⟩, fun p hp => ?_⟩
  apply Polynomial.map_injective j j.injective
  rw [hq, (IsAlgClosed.splits _).eq_prod_roots_of_monic (hp.1.map _)]
  change ((rootsBar p).map fun x => X - C x).prod = (S.map fun x => X - C x).prod
  rw [hp.2]

section Roots

variable {g : ℕ} [hg : Fact g.Prime]

structure GoodPoly (N : ℕ) (f : (ZMod g)[X]) : Prop where
  monic : f.Monic
  deg : f.natDegree = N
  coeff0 : f.coeff 0 ≠ 0
  sqf : Squarefree f

variable {N : ℕ} {f : (ZMod g)[X]}

private lemma map_ne_zero' (hf : GoodPoly N f) : f.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 :=
  (hf.monic.map _).ne_zero

lemma mem_rootsBar (hf : GoodPoly N f) {x : Fbar g} :
    x ∈ rootsBar f ↔ (f.map (algebraMap (ZMod g) (Fbar g))).eval x = 0 := by
  unfold rootsBar; rw [mem_roots (map_ne_zero' hf)]; rfl

lemma rootsBar_nodup (hf : GoodPoly N f) : (rootsBar f).Nodup :=
  nodup_roots ((PerfectField.separable_iff_squarefree.mpr hf.sqf).map)

lemma rootsBar_card (hf : GoodPoly N f) : (rootsBar f).card = N := by
  unfold rootsBar; rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hf.deg]

lemma ne_zero_of_mem (hf : GoodPoly N f) {x : Fbar g} (hx : x ∈ rootsBar f) : x ≠ 0 := by
  rintro rfl
  have h := (mem_rootsBar hf).mp hx
  rw [← coeff_zero_eq_eval_zero, coeff_map] at h
  exact hf.coeff0 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Fbar g)).injective).mp h)

private lemma pow_mem (hf : GoodPoly N f) {x : Fbar g} (hx : x ∈ rootsBar f) : x ^ g ∈ rootsBar f := by
  rw [GlobalTheory.GreenExists.mem_rootsBar_iff hf.monic.ne_zero] at hx ⊢
  simpa only [pow_one] using GlobalTheory.GreenExists.root_pow hx 1

lemma exists_index (hf : GoodPoly N f) : ∃ (r : Fin N → Fbar g) (σ : Equiv.Perm (Fin N)),
    Function.Injective r ∧ Finset.univ.val.map r = rootsBar f ∧ (∀ i, r (σ i) = r i ^ g) := by
  classical
  set Rt := (rootsBar f).toFinset
  have hc : Fintype.card Rt = N := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (rootsBar_nodup hf), rootsBar_card hf]
  set e := (Fintype.equivFinOfCardEq hc).symm
  set r : Fin N → Fbar g := fun i => (e i : Fbar g) with hrdef
  have hr : Function.Injective r := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ i, r i ∈ rootsBar f := fun i => Multiset.mem_toFinset.mp (e i).2
  have hsurj : ∀ x ∈ rootsBar f, ∃ i, r i = x := fun x hx =>
    ⟨e.symm ⟨x, Multiset.mem_toFinset.mpr hx⟩, by simp [r]⟩
  choose s hs using fun i => hsurj _ (pow_mem hf (hmem i))
  have hsinj : Function.Injective s := fun i j h => hr (frobenius_inj (Fbar g) g (by
    simp only [frobenius_def]; rw [← hs i, ← hs j, h]))
  refine ⟨r, Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj), hr, ?_,
    fun i => (hs i)⟩
  refine (Multiset.Nodup.ext (Multiset.Nodup.map hr Finset.univ.nodup) (rootsBar_nodup hf)).mpr ?_
  intro x; constructor
  · intro h; obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp h; exact hmem i
  · intro h; obtain ⟨i, rfl⟩ := hsurj x h; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)

variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}

lemma iter_eq (hσ : ∀ i, r (σ i) = r i ^ g) (n : ℕ) (i : Fin N) :
    r ((σ ^ n) i) = r i ^ (g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hσ, ih, ← pow_mul, pow_succ]

lemma exists_dvd (hf : GoodPoly N f) (hrf : Finset.univ.val.map r = rootsBar f)
    (hσ : ∀ i, r (σ i) = r i ^ g) (S : Finset (Fin N)) (hS : ∀ i ∈ S, σ i ∈ S) :
    ∃ Q : (ZMod g)[X], Q.Monic ∧ Q ∣ f ∧ Q.natDegree = S.card ∧
      ∀ i ∈ S, (Q.map (algebraMap (ZMod g) (Fbar g))).eval (r i) = 0 := by
  classical
  let j := algebraMap (ZMod g) (Fbar g)
  have hSσ : S.map σ.toEmbedding = S :=
    Finset.eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact hS x hx) (by rw [Finset.card_map])
  have hstable : (S.val.map r).map (fun x => x ^ g) = S.val.map r := by
    rw [Multiset.map_map]
    conv_rhs => rw [← hSσ, Finset.map_val, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i _
    exact (hσ i).symm
  obtain ⟨Q, ⟨hQm, hQroots⟩, -⟩ := existsUnique_monic_of_frobenius_stable _ hstable
  have hQle : rootsBar Q ≤ rootsBar f := by
    rw [hQroots, ← hrf]
    exact Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ S))
  have hQd : Q.natDegree = S.card := by
    calc
      Q.natDegree = (rootsBar Q).card := by
        rw [rootsBar, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
      _ = S.card := by rw [hQroots, Multiset.card_map, Finset.card_val]
  refine ⟨Q, hQm, ?_, hQd, ?_⟩
  · rw [← map_dvd_map j j.injective hQm]
    exact (IsAlgClosed.splits _).dvd_of_roots_le_roots (hQm.map _).ne_zero hQle
  · intro i hi
    apply (mem_roots (hQm.map _).ne_zero).mp
    change r i ∈ rootsBar Q
    rw [hQroots]
    exact Multiset.mem_map_of_mem _ hi

/-- The degree of an irreducible factor of prime degree is a Frobenius cycle length. -/
theorem mem_cycleType_of_factor (hf : GoodPoly N f) (hr : Function.Injective r)
    (hrf : Finset.univ.val.map r = rootsBar f) (hσ : ∀ i, r (σ i) = r i ^ g)
    (q : (ZMod g)[X]) (hq : Irreducible q) (hqf : q ∣ f) (hp : q.natDegree.Prime) :
    q.natDegree ∈ σ.cycleType := by
  classical
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) q (degree_pos_of_irreducible hq).ne'
  have hxf : x ∈ rootsBar f := by
    apply (GlobalTheory.GreenExists.mem_rootsBar_iff hf.monic.ne_zero).mpr
    obtain ⟨a, rfl⟩ := hqf
    rw [map_mul, hx, zero_mul]
  rw [← hrf] at hxf
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hxf
  have hperiod (m : ℕ) : (σ ^ m) i = i ↔ q.natDegree ∣ m := by
    rw [← hr.eq_iff, iter_eq hσ, hi]
    exact GlobalTheory.GreenExists.pow_eq_self_iff hq hx m
  have hmove : σ i ≠ i := by
    intro he
    exact hp.not_dvd_one ((hperiod 1).mp (by simpa only [pow_one] using he))
  let c := σ.cycleOf i
  have hc : c.IsCycle := Equiv.Perm.isCycle_cycleOf σ hmove
  have hcm : c i ≠ i := by
    change (σ.cycleOf i) i ≠ i
    rwa [Equiv.Perm.cycleOf_apply_self]
  have horder : orderOf c = q.natDegree := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      apply (hc.pow_eq_one_iff' hcm).mpr
      change ((σ.cycleOf i) ^ q.natDegree) i = i
      rw [Equiv.Perm.cycleOf_pow_apply_self]
      exact (hperiod _).mpr (dvd_refl _)
    · apply (hperiod _).mp
      rw [← Equiv.Perm.cycleOf_pow_apply_self]
      change (c ^ orderOf c) i = i
      rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]
  rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
  refine ⟨c, ?_, ?_⟩
  · exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hmove)
  · show c.support.card = _
    rw [← hc.orderOf, horder]

end Roots

end WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder
