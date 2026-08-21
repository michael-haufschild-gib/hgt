import GaloisForLFunctions.HTGeometry.GroupCharacter.Multiplicity
import GaloisForLFunctions.HTGeometry.GroupCharacter.ScalarCriterion
import GaloisForLFunctions.HTGeometry.GroupCharacter.Integrality

/-!
# Burnside's key lemma

A finite group with a conjugacy class of prime-power size `p ^ k`, `k ≥ 1`, has a proper nontrivial
normal subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra CategoryTheory

variable {G : Type} [Group G] [Fintype G]

/-- The conjugacy class of `x`, as a `Finset`. -/
def conjClass [DecidableEq G] (x : G) : Finset G :=
  Finset.image (fun g => g * x * g⁻¹) Finset.univ

theorem mem_conjClass [DecidableEq G] {x y : G} : y ∈ conjClass x ↔ IsConj x y := by
  simp [conjClass, isConj_iff, eq_comm]

theorem conjClass_stable [DecidableEq G] (x : G) :
    ∀ h : G, ∀ y ∈ conjClass x, h * y * h⁻¹ ∈ conjClass x := by
  intro h y hy
  rw [mem_conjClass] at hy ⊢
  exact hy.trans (isConj_iff.mpr ⟨h, rfl⟩)

theorem self_mem_conjClass [DecidableEq G] (x : G) : x ∈ conjClass x :=
  mem_conjClass.mpr (IsConj.refl x)

/-- If `x` is central then its conjugacy class is a singleton. -/
theorem conjClass_card_eq_one_of_mem_center [DecidableEq G] {x : G}
    (hx : ∀ g : G, g * x = x * g) : (conjClass x).card = 1 := by
  classical
  have : conjClass x = {x} := by
    ext y
    rw [mem_conjClass, Finset.mem_singleton]
    constructor
    · rintro h
      obtain ⟨c, hc⟩ := isConj_iff.mp h
      rw [← hc, hx c]
      group
    · rintro rfl
      exact IsConj.refl _
  rw [this, Finset.card_singleton]

end GaloisForLFunctions.HTGeometry.GroupCharacter

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra CategoryTheory

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- If the class of `x` has size coprime to `finrank N` and the action on `N` is faithful, then
either `chi` vanishes at `x` or `x` is central. -/
theorem chi_eq_zero_of_not_dvd {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N)
    (x : G) {p k : ℕ} (hp : p.Prime) (hKcard : (conjClass x).card = p ^ k)
    (hnd : ¬ p ∣ Module.finrank ℂ ↥N)
    (hcentral : ¬ (∀ g : G, g * x = x * g))
    (hfaithful : ∀ g : G, rho hN.stable g = LinearMap.id → g = 1) :
    chi hN.stable x = 0 := by
  classical
  rcases eq_or_ne (chi hN.stable x) 0 with hz | hne
  · exact hz
  exfalso
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr hN.ne_bot
  set d : ℕ := Module.finrank ℂ ↥N with hd
  have hd0 : d ≠ 0 := (Module.finrank_pos_iff.mpr inferInstance).ne'
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  obtain ⟨lam, hlamint, hlam⟩ := exists_classSum_scalar hN (conjClass x) (conjClass_stable x)
  have hconst : ∑ y ∈ conjClass x, chi hN.stable y = ((p : ℂ) ^ k) * chi hN.stable x := by
    have hterm : ∀ y ∈ conjClass x, chi hN.stable y = chi hN.stable x := by
      intro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp (mem_conjClass.mp hy)
      rw [← hc, chi_conj]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hKcard, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst] at hlam
  rw [← hd] at hlam
  -- Bezout
  have hcop : Nat.Coprime (p ^ k) d := Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hnd)
  have hbez : (1 : ℤ) = (p ^ k : ℕ) * Nat.gcdA (p ^ k) d + (d : ℕ) * Nat.gcdB (p ^ k) d := by
    have := Nat.gcd_eq_gcd_ab (p ^ k) d
    rwa [hcop, Nat.cast_one] at this
  set u : ℤ := Nat.gcdA (p ^ k) d with hu
  set v : ℤ := Nat.gcdB (p ^ k) d with hv
  have hbezC : ((p : ℂ) ^ k) * (u : ℂ) + (d : ℂ) * (v : ℂ) = 1 := by exact_mod_cast hbez.symm
  have hintegral : IsIntegral ℤ ((d : ℂ)⁻¹ * chi hN.stable x) := by
    have hidentity : (d : ℂ)⁻¹ * chi hN.stable x
        = (u : ℂ) * lam + (v : ℂ) * chi hN.stable x := by
      rw [inv_mul_eq_iff_eq_mul₀ hdC]
      linear_combination (-(u : ℂ)) * hlam - chi hN.stable x * hbezC
    rw [hidentity]
    have h1 : ((u : ℂ) * lam) ∈ integralClosure ℤ ℂ :=
      Subalgebra.mul_mem _ (by
        refine Subalgebra.algebraMap_mem _ u) hlamint
    have h2 : ((v : ℂ) * chi hN.stable x) ∈ integralClosure ℤ ℂ :=
      Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ v) (chi_isIntegral hN.stable x)
    exact Subalgebra.add_mem _ h1 h2
  obtain ⟨ε, hε⟩ := exists_rho_eq_smul hN.stable hN.ne_bot x hintegral hne
  -- `x` commutes with everything
  refine hcentral fun g => ?_
  have hcomm : rho hN.stable (x * g) = rho hN.stable (g * x) := by
    rw [rho_mul', rho_mul', hε, smul_mul_assoc, mul_smul_comm]
    rfl
  have hker : rho hN.stable ((x * g) * (g * x)⁻¹) = LinearMap.id := by
    rw [rho_mul', hcomm, ← rho_mul', mul_inv_cancel, rho_one]
  have := hfaithful _ hker
  rw [mul_inv_eq_one] at this
  exact this.symm

/-- **Burnside's key lemma.**  A finite group with a conjugacy class of size `p ^ k`, `k ≥ 1`, has a
proper nontrivial normal subgroup. -/
theorem exists_proper_normal_of_conjClass_prime_pow (x : G) (hx : x ≠ 1)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hKcard : (conjClass x).card = p ^ k) :
    ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ ∧ H ≠ ⊤ := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, N, hst, hbot, hminimal, hint⟩ := exists_simple_decomposition G
  have hN : ∀ i, IsMinimalGStable (N i) := fun i => ⟨hst i, hbot i, hminimal i⟩
  obtain ⟨i₀, hi₀triv, hi₀uniq⟩ := existsUnique_isTrivialOn hN hint
  have hpgt : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
  have hcentral : ¬ (∀ g : G, g * x = x * g) := by
    intro h
    rw [conjClass_card_eq_one_of_mem_center h] at hKcard
    omega
  have hfaith : ∀ i, ¬ IsTrivialOn (hN i).stable →
      ∀ g : G, rho (hN i).stable g = LinearMap.id → g = 1 := by
    intro i hi g hg
    have hkne : MonoidHom.ker (repOf (hN i).stable) ≠ ⊤ := by
      intro h
      refine hi (fun g' => ?_)
      have hg' : g' ∈ MonoidHom.ker (repOf (hN i).stable) := by
        rw [h]; exact Subgroup.mem_top g'
      exact MonoidHom.mem_ker.mp hg'
    have hkbot : MonoidHom.ker (repOf (hN i).stable) = ⊥ := by
      by_contra hb
      exact hkne (hcon _ inferInstance hb)
    have hgk : g ∈ MonoidHom.ker (repOf (hN i).stable) := MonoidHom.mem_ker.mpr hg
    rw [hkbot, Subgroup.mem_bot] at hgk
    exact hgk
  have hsum0 : ∑ i, chi (hN i).stable x = 0 := by
    have h := sum_chi (fun i => (hN i).stable) hint x
    rwa [if_neg hx] at h
  have hfin0 : Module.finrank ℂ ↥(N i₀) = 1 := finrank_eq_one_of_isTrivialOn (hN i₀) hi₀triv
  have hchi0 : chi (hN i₀).stable x = 1 := by
    rw [chi, hi₀triv x, LinearMap.trace_id, hfin0]
    norm_num
  have hvanish : ∀ i, i ≠ i₀ → ¬ p ∣ Module.finrank ℂ ↥(N i) → chi (hN i).stable x = 0 := by
    intro i hii hnd
    refine chi_eq_zero_of_not_dvd (hN i) x hp hKcard hnd hcentral (hfaith i ?_)
    intro htriv
    exact hii (hi₀uniq i htriv)
  -- the divisible part sums to `-1`
  have hi₀notP : ¬ p ∣ Module.finrank ℂ ↥(N i₀) := by
    rw [hfin0]
    exact fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_one h)
  have hcompl : ∑ i ∈ Finset.univ.filter (fun i => ¬ p ∣ Module.finrank ℂ ↥(N i)),
      chi (hN i).stable x = 1 := by
    rw [Finset.sum_eq_single i₀]
    · exact hchi0
    · intro i hi hii
      exact hvanish i hii (Finset.mem_filter.mp hi).2
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀notP⟩) h
  have hPsum : ∑ i ∈ Finset.univ.filter (fun i => p ∣ Module.finrank ℂ ↥(N i)),
      chi (hN i).stable x = -1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => p ∣ Module.finrank ℂ ↥(N i)) (fun i => chi (hN i).stable x)
    rw [hcompl, hsum0] at hsplit
    linear_combination hsplit
  -- group the divisible part by isomorphism class
  set cls : Fin n → Finset (Fin n) := fun i =>
    Finset.univ.filter fun j => Nonempty (fdRepOf (hN j).stable ≅ fdRepOf (hN i).stable) with hcls
  have hmem_cls : ∀ i j, j ∈ cls i ↔ Nonempty (fdRepOf (hN j).stable ≅ fdRepOf (hN i).stable) := by
    intro i j
    simp [hcls]
  have hself_cls : ∀ i, i ∈ cls i := fun i => (hmem_cls i i).mpr ⟨Iso.refl _⟩
  have hcls_eq : ∀ i j, Nonempty (fdRepOf (hN i).stable ≅ fdRepOf (hN j).stable) →
      cls i = cls j := by
    intro i j ⟨e⟩
    ext l
    rw [hmem_cls, hmem_cls]
    exact ⟨fun ⟨f⟩ => ⟨f.trans e⟩, fun ⟨f⟩ => ⟨f.trans e.symm⟩⟩
  set r : Fin n → Fin n := fun i => (cls i).min' ⟨i, hself_cls i⟩ with hr
  have hr_mem : ∀ i, r i ∈ cls i := fun i => Finset.min'_mem _ _
  have hr_idem : ∀ i, r (r i) = r i := by
    intro i
    have hEq : cls (r i) = cls i := hcls_eq _ _ ((hmem_cls i (r i)).mp (hr_mem i))
    show (cls (r i)).min' _ = (cls i).min' _
    simp only [hEq]
  have hr_eq_iff : ∀ i j, r i = r j ↔
      Nonempty (fdRepOf (hN i).stable ≅ fdRepOf (hN j).stable) := by
    intro i j
    constructor
    · intro h
      obtain ⟨e1⟩ := (hmem_cls i (r i)).mp (hr_mem i)
      obtain ⟨e2⟩ := (hmem_cls j (r j)).mp (hr_mem j)
      rw [h] at e1
      exact ⟨e1.symm.trans e2⟩
    · intro h
      show (cls i).min' _ = (cls j).min' _
      simp only [hcls_eq _ _ h]
  have hchi_iso : ∀ i j, Nonempty (fdRepOf (hN i).stable ≅ fdRepOf (hN j).stable) →
      chi (hN i).stable x = chi (hN j).stable x := by
    intro i j ⟨e⟩
    have := FDRep.char_iso e
    have h2 := congrFun this x
    rwa [character_fdRepOf, character_fdRepOf] at h2
  have hfinrank_iso : ∀ i j, Nonempty (fdRepOf (hN i).stable ≅ fdRepOf (hN j).stable) →
      Module.finrank ℂ ↥(N i) = Module.finrank ℂ ↥(N j) := by
    intro i j hij
    have h1 : chi (hN i).stable 1 = chi (hN j).stable 1 := by
      obtain ⟨e⟩ := hij
      have h2 := congrFun (FDRep.char_iso e) 1
      rwa [character_fdRepOf, character_fdRepOf] at h2
    rw [chi_one, chi_one] at h1
    exact_mod_cast h1
  set P : Finset (Fin n) := Finset.univ.filter (fun i => p ∣ Module.finrank ℂ ↥(N i)) with hP
  have hPmem : ∀ c, c ∈ P → p ∣ Module.finrank ℂ ↥(N c) := by
    intro c hc
    rw [hP, Finset.mem_filter] at hc
    exact hc.2
  have hrP : ∀ i ∈ P, r i ∈ P := by
    intro i hi
    rw [hP, Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hfinrank_iso (r i) i ((hmem_cls i (r i)).mp (hr_mem i))]
    exact hi.2
  have himP : ∀ c ∈ P.image r, c ∈ P := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    exact hrP i hi
  have hrfix : ∀ c ∈ P.image r, r c = c := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    exact hr_idem i
  have hfiber : ∀ c ∈ P.image r, P.filter (fun i => r i = c) = cls c := by
    intro c hc
    have hrc := hrfix c hc
    have hcP := himP c hc
    ext j
    rw [Finset.mem_filter, hmem_cls]
    constructor
    · rintro ⟨-, hj⟩
      exact (hr_eq_iff j c).mp (by rw [hj, hrc])
    · intro hj
      have hjc : r j = c := by rw [(hr_eq_iff j c).mpr hj, hrc]
      refine ⟨?_, hjc⟩
      rw [hP, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hfinrank_iso j c hj]
      exact hPmem c hcP
  have hsum_fiber : ∀ c ∈ P.image r, ∑ i ∈ P.filter (fun i => r i = c), chi (hN i).stable x
      = (Module.finrank ℂ ↥(N c) : ℂ) * chi (hN c).stable x := by
    intro c hc
    rw [hfiber c hc,
      Finset.sum_congr rfl (fun j hj => hchi_iso j c ((hmem_cls c j).mp hj)),
      Finset.sum_const, nsmul_eq_mul]
    congr 1
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (card_iso_eq_finrank hN hint c)
  have hgroup := Finset.sum_fiberwise_of_maps_to (s := P) (t := P.image r) (g := r)
    (fun i hi => Finset.mem_image_of_mem r hi) (fun i => chi (hN i).stable x)
  rw [hPsum, Finset.sum_congr rfl hsum_fiber] at hgroup
  set β : ℂ := ∑ c ∈ P.image r,
    ((Module.finrank ℂ ↥(N c) / p : ℕ) : ℂ) * chi (hN c).stable x with hβ
  have hpβ : (p : ℂ) * β = -1 := by
    rw [hβ, Finset.mul_sum, ← hgroup]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hdvd : p ∣ Module.finrank ℂ ↥(N c) := hPmem c (himP c hc)
    rw [← mul_assoc]
    congr 1
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  have hβint : IsIntegral ℤ β := by
    show β ∈ integralClosure ℤ ℂ
    rw [hβ]
    refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun c _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) ?_
    exact chi_isIntegral (hN c).stable x
  -- the contradiction: `-1/p` would be a rational algebraic integer
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hβval : β = ((-1 / (p : ℚ) : ℚ) : ℂ) := by
    have hcast : ((-1 / (p : ℚ) : ℚ) : ℂ) = -1 / (p : ℂ) := by push_cast; ring
    rw [hcast, eq_div_iff hpC]
    linear_combination hpβ
  have hqint : IsIntegral ℤ ((-1 / (p : ℚ) : ℚ)) := by
    refine IsIntegral.tower_bot (R := ℤ) (A := ℚ) (B := ℂ) ?_ ?_
    · exact fun a b hab => by exact_mod_cast hab
    · rw [show (algebraMap ℚ ℂ) ((-1 / (p : ℚ) : ℚ)) = ((-1 / (p : ℚ) : ℚ) : ℂ) from rfl, ← hβval]
      exact hβint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
  have hzq : (z : ℚ) = -1 / (p : ℚ) := by exact_mod_cast hz
  have hpQ : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hzp : (z : ℚ) * (p : ℚ) = -1 := by
    rw [hzq]
    field_simp
  have hzpZ : z * (p : ℤ) = -1 := by exact_mod_cast hzp
  have : (p : ℤ) ∣ 1 := ⟨-z, by linarith [hzpZ]⟩
  have hp1 : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one this)
  rcases hp1 with h | h
  · exact hp.one_lt.ne' (by exact_mod_cast h)
  · have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
    omega

end GaloisForLFunctions.HTGeometry.GroupCharacter
