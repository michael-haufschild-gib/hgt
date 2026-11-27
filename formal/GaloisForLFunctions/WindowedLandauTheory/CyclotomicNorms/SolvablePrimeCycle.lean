import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.PrimeCycleBlocks

/-! A transitive solvable action cannot contain a prime cycle moving more
than half the points and leaving at least two fixed points. The last nontrivial
derived subgroup acts regularly, so the number of fixed points divides the degree. -/

open scoped Classical commutatorElement
open Finset MulAction

namespace WindowedLandauTheory.CyclotomicNorms

private theorem image_orbit_finset {G Ω : Type} [Group G] [MulAction G Ω] [Fintype Ω]
    [DecidableEq Ω]
    (H : Subgroup G) [H.Normal] (g : G) (x : Ω) :
    (orbit H x).toFinset.image (fun y => g • y) = (orbit H (g • x)).toFinset := by
  ext y
  simp only [Finset.mem_image, Set.mem_toFinset, mem_orbit_iff]
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    refine ⟨⟨g * (h : G) * g⁻¹, (inferInstance : H.Normal).conj_mem _ h.2 _⟩, ?_⟩
    change (g * (h : G) * g⁻¹) • (g • x) = g • ((h : G) • x)
    simp only [mul_smul, inv_smul_smul]
  · rintro ⟨h, rfl⟩
    let k : H := ⟨g⁻¹ * (h : G) * g, by
      simpa only [inv_inv] using (inferInstance : H.Normal).conj_mem _ h.2 g⁻¹⟩
    refine ⟨k • x, ⟨k, rfl⟩, ?_⟩
    change g • ((g⁻¹ * (h : G) * g) • x) = (h : G) • (g • x)
    simp only [mul_smul, smul_inv_smul]

private theorem normal_pretransitive_of_prime_cycle {G Ω : Type} [Group G] [MulAction G Ω]
    [FaithfulSMul G Ω] [Fintype Ω] [deq : DecidableEq Ω] (tr : MulAction.IsPretransitive G Ω)
    (H : Subgroup G) [H.Normal] (hH : H ≠ ⊥) (g : G) (p : ℕ) (hp : p.Prime)
    (hdeg : Fintype.card Ω < 2 * p)
    (hcyc : (MulAction.toPerm g : Equiv.Perm Ω).IsCycle)
    (hsupp : (MulAction.toPerm g : Equiv.Perm Ω).support.card = p) (x₀ : Ω) :
    MulAction.IsPretransitive H Ω := by
  classical
  letI : DecidableEq Ω := deq
  let b (x : Ω) := (orbit H x).toFinset
  let B := Finset.univ.image b
  have hm (x : Ω) : (b x).card = (b x₀).card := by
    obtain ⟨a, rfl⟩ := tr.exists_smul_eq x₀ x
    rw [show b (a • x₀) = (b x₀).image (fun y => a • y) from (image_orbit_finset H a x₀).symm]
    exact Finset.card_image_of_injective _ (show Function.Injective (fun y : Ω => a • y) from
      (MulAction.toPerm a).injective)
  have hsize (c : Finset Ω) (hc : c ∈ B) : c.card = (b x₀).card := by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
    exact hm x
  have hdisj (c : Finset Ω) (hc : c ∈ B) (d : Finset Ω) (hd : d ∈ B) (hcd : c ≠ d) :
      Disjoint c d := by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hd
    refine Finset.disjoint_left.mpr fun z hzx hzy => hcd ?_
    have hx : orbit H z = orbit H x := orbit_eq_iff.mpr (Set.mem_toFinset.mp hzx)
    have hy : orbit H z = orbit H y := orbit_eq_iff.mpr (Set.mem_toFinset.mp hzy)
    simp only [b, hx.symm.trans hy]
  have hcover (x : Ω) : ∃ c ∈ B, x ∈ c :=
    ⟨b x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, Set.mem_toFinset.mpr (mem_orbit_self x)⟩
  have hinv (a : G) (c : Finset Ω) (hc : c ∈ B) : c.image (fun x => a • x) ∈ B := by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨a • x, Finset.mem_univ _, (image_orbit_finset H a x).symm⟩
  rcases blocks_form_cycle G Ω B (b x₀).card p g hsize hdisj hcover hinv hp hdeg hcyc hsupp with hc | hc
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
    have hb (x : Ω) : b x = c := by
      have hx : b x ∈ B := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
      rwa [hc, Finset.mem_singleton] at hx
    refine ⟨fun x y => mem_orbit_iff.mp (Set.mem_toFinset.mp ?_)⟩
    change y ∈ b x
    rw [hb x, ← hb y]
    exact Set.mem_toFinset.mpr (mem_orbit_self y)
  · have hu : B.biUnion (fun c => c) = Finset.univ := Finset.eq_univ_of_forall fun x =>
      Finset.mem_biUnion.mpr (hcover x)
    have ht : Fintype.card Ω = B.card * (b x₀).card := by
      rw [← Finset.card_univ, ← hu, Finset.card_biUnion hdisj]
      exact Finset.sum_const_nat hsize
    have hm₁ : (b x₀).card = 1 := by
      rw [hc] at ht
      exact Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.mpr ⟨x₀⟩)
        (by rw [mul_one]; exact ht.symm)
    exfalso
    apply hH
    apply le_antisymm _ bot_le
    intro a ha
    apply Subgroup.mem_bot.mpr
    apply (eq_of_smul_eq_smul (α := Ω))
    intro x
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp ((hm x).trans hm₁)
    have hx : x ∈ b x := Set.mem_toFinset.mpr (mem_orbit_self x)
    have hax : a • x ∈ b x := Set.mem_toFinset.mpr ((mem_orbit_iff).mpr ⟨⟨a, ha⟩, rfl⟩)
    rw [hy, Finset.mem_singleton] at hx hax
    simpa only [one_smul] using hax.trans hx.symm

private theorem orbitEquiv_of_commutative {G Ω : Type} [Group G] [MulAction G Ω]
    [FaithfulSMul G Ω] (H : Subgroup G) [IsMulCommutative H]
    (tr : MulAction.IsPretransitive H Ω) (x : Ω) :
    ∃ e : H ≃ Ω, ∀ h, e h = h • x := by
  refine ⟨Equiv.ofBijective (fun h : H => h • x) ⟨?_, tr.exists_smul_eq x⟩, fun _ => rfl⟩
  intro a b hab
  apply Subtype.ext
  apply (eq_of_smul_eq_smul (α := Ω))
  intro y
  obtain ⟨c, rfl⟩ := tr.exists_smul_eq x y
  change a • x = b • x at hab
  change a • (c • x) = b • (c • x)
  rw [← mul_smul, ← mul_smul, mul_comm' a c, mul_comm' b c, mul_smul, mul_smul, hab]

private theorem fixed_card_dvd_of_normal_regular {G Ω : Type} [Group G] [MulAction G Ω]
    [Fintype Ω] [deq : DecidableEq Ω] (H : Subgroup G) [H.Normal] (g : G) (x : Ω) (hx : g • x = x)
    (e : H ≃ Ω) (he : ∀ h, e h = h • x) :
    ((MulAction.toPerm g : Equiv.Perm Ω).supportᶜ).card ∣ Fintype.card Ω := by
  classical
  letI : DecidableEq Ω := deq
  let C := (Subgroup.centralizer ({g} : Set G)).comap H.subtype
  have hiff (h : H) : h ∈ C ↔ e h ∈ (MulAction.toPerm g : Equiv.Perm Ω).supportᶜ := by
    have hl : h ∈ C ↔ g * (h : G) = (h : G) * g := by
      change (h : G) ∈ Subgroup.centralizer ({g} : Set G) ↔ _
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    rw [hl, Finset.mem_compl, Equiv.Perm.notMem_support, he]
    change (g * (h : G) = (h : G) * g) ↔ g • ((h : G) • x) = (h : G) • x
    constructor
    · intro hc
      rw [← mul_smul, hc, mul_smul, hx]
    · intro hs
      let h' : H := ⟨g * (h : G) * g⁻¹, (inferInstance : H.Normal).conj_mem _ h.2 _⟩
      have h'e : e h' = e h := by
        rw [he, he]
        change (g * (h : G) * g⁻¹) • x = (h : G) • x
        have hxi : g⁻¹ • x = x :=
          (congrArg (fun y => g⁻¹ • y) hx.symm).trans (inv_smul_smul g x)
        simpa only [mul_smul, hxi] using hs
      have hc := congrArg Subtype.val (e.injective h'e)
      change g * (h : G) * g⁻¹ = (h : G) at hc
      calc
        g * (h : G) = (g * (h : G) * g⁻¹) * g := by group
        _ = (h : G) * g := by rw [hc]
  let E := e.subtypeEquiv hiff
  have hC : Nat.card C = ((MulAction.toPerm g : Equiv.Perm Ω).supportᶜ).card :=
    (Nat.card_congr E).trans (by rw [Nat.card_eq_fintype_card, Fintype.card_coe])
  have hH : Nat.card H = Fintype.card Ω :=
    (Nat.card_congr e).trans Nat.card_eq_fintype_card
  rw [← hC, ← hH]
  exact Subgroup.card_subgroup_dvd_card C

/-- A prime cycle covering more than half a transitive action has at most one
fixed point if the acting group is solvable. -/
theorem not_isSolvable_of_long_prime_cycle {G Ω : Type} [Group G] [MulAction G Ω]
    [Fintype Ω] [deq : DecidableEq Ω] (tr : MulAction.IsPretransitive G Ω)
    (g : G) {p : ℕ} (hp : p.Prime) (hdeg : Fintype.card Ω < 2 * p)
    (hfix : p + 2 ≤ Fintype.card Ω)
    (hcyc : (MulAction.toPerm g : Equiv.Perm Ω).IsCycle)
    (hsupp : (MulAction.toPerm g : Equiv.Perm Ω).support.card = p) : ¬ IsSolvable G := by
  classical
  letI : DecidableEq Ω := deq
  intro hsolv
  letI : IsSolvable G := hsolv
  let f := MulAction.toPermHom G Ω
  let K := f.range
  let a : K := ⟨f g, ⟨g, rfl⟩⟩
  have ha : a ≠ 1 := fun h => hcyc.ne_one (congrArg Subtype.val h)
  letI : IsSolvable K := solvable_of_surjective f.rangeRestrict_surjective
  letI : FaithfulSMul K Ω :=
    ⟨fun h => Subtype.ext (Equiv.ext h)⟩
  have htr : MulAction.IsPretransitive K Ω := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := tr.exists_smul_eq x y
    exact ⟨f.rangeRestrict g, hg⟩
  have hzero : ∃ n : ℕ, derivedSeries K n = ⊥ := IsSolvable.solvable
  have hbot := Nat.find_spec hzero
  have hn₀ : Nat.find hzero ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at hbot
    apply ha
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact Subgroup.mem_top a
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
  let H := derivedSeries K n
  letI : H.Normal := derivedSeries_normal K n
  have hH : H ≠ ⊥ := Nat.find_min hzero (by rw [hn]; exact Nat.lt_succ_self _)
  have hcomm : IsMulCommutative H := by
    apply Subgroup.commutator_self_eq_bot_iff.mp
    rw [hn, derivedSeries_succ] at hbot
    exact hbot
  letI : IsMulCommutative H := hcomm
  let C := ((MulAction.toPerm g : Equiv.Perm Ω).supportᶜ)
  have hc : C.card = Fintype.card Ω - p := by
    rw [Finset.card_compl, hsupp]
  obtain ⟨x, hx⟩ : C.Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
  have hax : a • x = x := Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp hx)
  have hperm : (MulAction.toPerm a : Equiv.Perm Ω) = MulAction.toPerm g := Equiv.ext fun _ => rfl
  have hcyc' : (MulAction.toPerm a : Equiv.Perm Ω).IsCycle := by rw [hperm]; exact hcyc
  have hsupp' : (MulAction.toPerm a : Equiv.Perm Ω).support.card = p := by rw [hperm]; exact hsupp
  have htrH := normal_pretransitive_of_prime_cycle htr H hH a p hp hdeg hcyc' hsupp' x
  obtain ⟨e, he⟩ := orbitEquiv_of_commutative H htrH x
  have hdvd := fixed_card_dvd_of_normal_regular H a x hax e he
  rw [hperm, Finset.card_compl, hsupp] at hdvd
  have hdivp : Fintype.card Ω - p ∣ p := by
    have h := Nat.dvd_sub hdvd (dvd_refl (Fintype.card Ω - p))
    simpa only [Nat.sub_sub_self (show p ≤ Fintype.card Ω by omega)] using h
  rcases (Nat.dvd_prime hp).mp hdivp with h | h <;> omega

end WindowedLandauTheory.CyclotomicNorms
