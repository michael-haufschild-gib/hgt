import GaloisForLFunctions.AdelicKreinGeometry.ThreePrimesCarryTheWholeAffineState

/-!
# Principal S-unit logarithmic support boundary

For finite prime sets `S,T`, impose arbitrary principal-unit depths at every
prime in `T` on positive `S`-units. Unit norms delete exactly the valuation
coordinates in `S ∩ T`. The logarithms are dense precisely when `S \ T`
contains two distinct primes; one remaining prime gives a nonzero cyclic
lattice, and none gives the trivial group.

A common Euler power supplies the simultaneous congruences. In the dense
case the full negative and mass-zero Weil indices survive, every global
correlation value remains approximable, and one positive oscillation works
uniformly across all finite supports, selected places, and depths.
-/

noncomputable section
open Complex Finset Set Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

namespace GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- Positive rational units whose valuation support lies in `S`. -/
def supported (S : Finset Nat.Primes) : Subgroup posUnits :=
  ⨅ p : Nat.Primes, ⨅ _ : p ∉ S, (towerVal (p : ℕ)).ker

/-- Membership is exactly vanishing of all valuations outside the allowed support. -/
theorem mem_supported (S : Finset Nat.Primes) (u : posUnits) :
    u ∈ supported S ↔ ∀ p : Nat.Primes, p ∉ S →
      padicValRat (p : ℕ) (((u : ℚˣ) : ℚ)) = 0 := by
  simp only [supported, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl

/-- Simultaneous principal-unit conditions at the selected finite places. -/
def principal (T : Finset Nat.Primes) (n : Nat.Primes → ℕ) : Subgroup posUnits :=
  ⨅ p : T, padicPrincipalUnits (p : Nat.Primes) (n p)

/-- The finite intersection imposes the stated condition at each selected prime. -/
theorem mem_principal (T : Finset Nat.Primes) (n : Nat.Primes → ℕ) (u : posUnits) :
    u ∈ principal T n ↔ ∀ p ∈ T, u ∈ padicPrincipalUnits (p : Nat.Primes) (n p) := by
  simp only [principal, Subgroup.mem_iInf, Subtype.forall]

/-- Positive `S`-units subject to all principal-unit conditions in `T`. -/
def group (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ) : Subgroup posUnits :=
  supported S ⊓ principal T n

private theorem prime_mem_supported {S : Finset Nat.Primes} {q : Nat.Primes} (hq : q ∈ S) :
    primeUnit q ∈ supported S := by
  apply (mem_supported S _).mpr
  intro p hp
  have hne : q ≠ p := fun h => hp (h ▸ hq)
  have h := towerVal_primePos q p
  rw [if_neg hne] at h
  exact congrArg Multiplicative.toAdd h

private theorem supported_mono {S T : Finset Nat.Primes} (hST : S ⊆ T) :
    supported S ≤ supported T := by
  intro u hu
  apply (mem_supported T u).mpr
  exact fun p hp => (mem_supported S u).mp hu p (fun hs => hp (hST hs))

private theorem supported_product {S : Finset Nat.Primes} {u : posUnits}
    (hu : u ∈ supported S) :
    u = ∏ p ∈ S, primeUnit p ^ padicValRat (p : ℕ) (((u : ℚˣ) : ℚ)) := by
  let e := valFinsupp (((u : ℚˣ) : ℚ))
  have he : e.support ⊆ S := by
    intro p hp
    by_contra hps
    exact Finsupp.mem_support_iff.mp hp ((mem_supported S u).mp hu p hps)
  calc u = finsuppUnit e := (finsuppUnit_valFinsupp u).symm
       _ = ∏ p ∈ S, primeUnit p ^ e p :=
         Finsupp.prod_of_support_subset e he (fun p k => primeUnit p ^ k)
           (fun _ _ => zpow_zero _)
       _ = _ := rfl

private theorem common_prime_power (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (hST : Disjoint S T) :
    ∃ M : ℕ, 0 < M ∧ ∀ q ∈ S, primeUnit q ^ M ∈ principal T n := by
  classical
  induction T using Finset.induction with
  | empty =>
    refine ⟨1, zero_lt_one, fun q hq => (mem_principal _ _ _).mpr ?_⟩
    simp only [Finset.notMem_empty, false_implies, implies_true]
  | @insert p T hp ih =>
    have hST' : Disjoint S T := hST.mono_right (subset_insert p T)
    obtain ⟨M, hM, hm⟩ := ih hST'
    have hpos : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
      (by positivity : 0 < ((n p : ℝ) + 1)⁻¹) (inv_lt_one_of_one_lt₀ hpos)
    let K := ((p : ℕ) ^ k).totient
    have hK : 0 < K := Nat.totient_pos.mpr (pow_pos p.2.pos k)
    refine ⟨K * M, Nat.mul_pos hK hM, fun q hq => (mem_principal _ _ _).mpr ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with hrp | hr
    · subst r
      have hpq : p ≠ q := fun h => (Finset.disjoint_left.mp hST hq) (h ▸ mem_insert_self p T)
      rw [pow_mul]
      exact (padicPrincipalUnits (p : ℕ) (n p)).pow_mem
        (prime_power_mem_principal p q hpq (n p) k hk) M
    · rw [Nat.mul_comm K M, pow_mul]
      exact (padicPrincipalUnits (r : ℕ) (n r)).pow_mem
        ((mem_principal T n _).mp (hm q hq) r hr) K

/-- A single positive power sends every supported unit into all selected principal subgroups. -/
theorem common_supported_power (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (hST : Disjoint S T) :
    ∃ M : ℕ, 0 < M ∧ ∀ u : supported S, (u : posUnits) ^ M ∈ group S T n := by
  obtain ⟨M, hM, hm⟩ := common_prime_power S T n hST
  refine ⟨M, hM, fun u => ⟨(supported S).pow_mem u.2 M, ?_⟩⟩
  rw [supported_product u.2, ← Finset.prod_pow]
  apply (principal T n).prod_mem
  intro q hq
  rw [← zpow_natCast (primeUnit q ^ padicValRat (q : ℕ) (((u : posUnits) : ℚˣ) : ℚ)) M,
    ← zpow_mul, mul_comm _ (M : ℤ), zpow_mul, zpow_natCast]
  exact (principal T n).zpow_mem (hm q hq) _

private theorem valuation_zero_of_principal {p : Nat.Primes} {n : ℕ} {u : posUnits}
    (hu : u ∈ padicPrincipalUnits (p : ℕ) n) :
    padicValRat (p : ℕ) (((u : ℚˣ) : ℚ)) = 0 := by
  have hp : (1 : ℚ) < p := by exact_mod_cast p.2.one_lt
  have hnorm : padicNorm (p : ℕ) (((u : ℚˣ) : ℚ)) = 1 := by
    have h := hu.1
    rw [Rat.AbsoluteValue.padic_eq_padicNorm] at h
    exact_mod_cast h
  rw [padicNorm.eq_zpow_of_nonzero (Units.ne_zero _)] at hnorm
  have h := (zpow_right_strictMono₀ hp).injective
    (hnorm.trans (zpow_zero (p : ℚ)).symm)
  exact neg_eq_zero.mp h

/-- Local unit norms remove precisely the selected valuation coordinates. -/
theorem delete_local_support (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    group S T n = group (S \ T) T n := by
  apply le_antisymm
  · rintro u ⟨huS, huT⟩
    refine ⟨(mem_supported _ _).mpr ?_, huT⟩
    intro p hp
    by_cases hpT : p ∈ T
    · exact valuation_zero_of_principal ((mem_principal _ _ _).mp huT p hpT)
    · exact (mem_supported S u).mp huS p
        (fun hpS => hp (mem_sdiff.mpr ⟨hpS, hpT⟩))
  · exact inf_le_inf (supported_mono sdiff_subset) le_rfl

private theorem supported_empty_eq_one {u : posUnits} (hu : u ∈ supported ∅) : u = 1 := by
  rw [supported_product hu, Finset.prod_empty]

private theorem supported_singleton {q : Nat.Primes} {u : posUnits}
    (hu : u ∈ supported {q}) :
    u = primeUnit q ^ padicValRat (q : ℕ) (((u : ℚˣ) : ℚ)) := by
  simpa only [Finset.prod_singleton] using supported_product hu

private theorem log_near_of_two_free_primes {S T : Finset Nat.Primes}
    (n : Nat.Primes → ℕ) {q r : Nat.Primes} (hq : q ∈ S \ T)
    (hr : r ∈ S \ T) (hqr : q ≠ r) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : group S T n, |logPos (u : posUnits) - t| < ε := by
  have hdis : Disjoint (S \ T) T := Finset.disjoint_left.mpr
    (fun p hp ht => (Finset.mem_sdiff.mp hp).2 ht)
  obtain ⟨M, hMnat, hm⟩ := common_supported_power (S \ T) T n hdis
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr hMnat
  have htwo : twoPrimeUnits q r ≤ supported (S \ T) := by
    apply (Subgroup.closure_le (supported (S \ T))).mpr
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact prime_mem_supported hq
    · rw [Set.mem_singleton_iff.mp hu]
      exact prime_mem_supported hr
  obtain ⟨v, hv, u, rfl⟩ := Metric.dense_iff.mp (dense_range_logPos_twoPrimeUnits hqr)
    (t / M) (ε / M) (div_pos hε hM)
  have hu : |logPos (u : posUnits) - t / M| < ε / M := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hv
  let v : group S T n := ⟨(u : posUnits) ^ M, by
    rw [delete_local_support S T n]
    exact hm ⟨u, htwo u.2⟩⟩
  have hv : logPos (v : posUnits) = (M : ℝ) * logPos (u : posUnits) := by
    simpa only [v, zpow_natCast, Int.cast_natCast] using logPos_zpow (u : posUnits) (M : ℤ)
  refine ⟨v, ?_⟩
  calc |logPos (v : posUnits) - t|
      = (M : ℝ) * |logPos (u : posUnits) - t / M| := by
        rw [hv, show (M : ℝ) * logPos (u : posUnits) - t =
          (M : ℝ) * (logPos (u : posUnits) - t / M) by
            rw [mul_sub, mul_div_cancel₀ _ hM.ne'], abs_mul, abs_of_pos hM]
    _ < (M : ℝ) * (ε / M) := mul_lt_mul_of_pos_left hu hM
    _ = ε := mul_div_cancel₀ _ hM.ne'

/-- The actual real logarithms of a positive rational subgroup. -/
def logGroup (H : Subgroup posUnits) : AddSubgroup ℝ where
  carrier := Set.range (fun u : H => logPos (u : posUnits))
  zero_mem' := ⟨1, logPos_one⟩
  add_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, logPos_mul u v⟩
  neg_mem' := by
    rintro _ ⟨u, rfl⟩
    refine ⟨u⁻¹, ?_⟩
    change logPos ((u : posUnits)⁻¹) = -logPos (u : posUnits)
    simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul]
      using logPos_zpow (u : posUnits) (-1)

private theorem logGroup_le_of_supported_singleton {H : Subgroup posUnits} {q : Nat.Primes}
    (hH : H ≤ supported {q}) : logGroup H ≤ AddSubgroup.zmultiples (Real.log (q : ℕ)) := by
  rintro t ⟨u, rfl⟩
  change logPos (u : posUnits) ∈ AddSubgroup.zmultiples (Real.log (q : ℕ))
  rw [supported_singleton (hH u.2), logPos_zpow, logPos_primeUnit]
  exact ⟨padicValRat (q : ℕ) (((u : posUnits) : ℚˣ) : ℚ), by simp only [zsmul_eq_mul]⟩

/-- Constraining every allowed prime to be a unit leaves only the positive rational one. -/
theorem group_eq_bot_of_no_free_primes {S T : Finset Nat.Primes}
    (n : Nat.Primes → ℕ) (h : S \ T = ∅) : group S T n = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [delete_local_support S T n, h] at hu
  exact supported_empty_eq_one hu.1

private theorem not_dense_logGroup_of_card_le_one {S T : Finset Nat.Primes}
    (n : Nat.Primes → ℕ) (h : (S \ T).card ≤ 1) :
    ¬ Dense (logGroup (group S T n) : Set ℝ) := by
  intro hd
  by_cases he : S \ T = ∅
  · have hz : (logGroup (group S T n) : Set ℝ) ⊆ (AddSubgroup.zmultiples (0 : ℝ) : Set ℝ) := by
      rintro t ⟨u, rfl⟩
      have hu : (u : posUnits) = 1 := by
        have hmem := u.2
        exact (show group S T n ≤ ⊥ from le_of_eq (group_eq_bot_of_no_free_primes n he)) hmem
      change logPos (u : posUnits) ∈ AddSubgroup.zmultiples (0 : ℝ)
      rw [hu, logPos_one]
      exact (AddSubgroup.zmultiples (0 : ℝ)).zero_mem
    exact not_denseRange_zsmul (hd.mono hz)
  · obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hs : S \ T ⊆ {q} := fun r hr =>
      Finset.mem_singleton.mpr (Finset.card_le_one.mp h r hr q hq)
    have hsub : group S T n ≤ supported {q} := by
      rw [delete_local_support S T n]
      exact inf_le_left.trans (supported_mono hs)
    exact not_denseRange_zsmul (hd.mono (logGroup_le_of_supported_singleton hsub))

private theorem two_free_primes {F : Finset Nat.Primes} (h : 2 ≤ F.card) :
    ∃ q ∈ F, ∃ r ∈ F, q ≠ r := by
  by_contra hn
  push Not at hn
  have hc := Finset.card_le_one.mpr hn
  omega

/-- Logarithmic density is equivalent to having at least two free prime directions. -/
theorem dense_logGroup_iff (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ) :
    Dense (logGroup (group S T n) : Set ℝ) ↔ 2 ≤ (S \ T).card := by
  constructor
  · intro hd
    by_contra h
    exact not_dense_logGroup_of_card_le_one n (by omega) hd
  · intro h
    obtain ⟨q, hq, r, hr, hqr⟩ := two_free_primes h
    apply Metric.dense_iff.mpr
    intro t ε hε
    obtain ⟨u, hu⟩ := log_near_of_two_free_primes n hq hr hqr t hε
    exact ⟨logPos (u : posUnits), by simpa only [Metric.mem_ball, Real.dist_eq] using hu,
      u, rfl⟩

/-- One free prime leaves exactly a nonzero integer sublattice of its logarithmic tower. -/
theorem cyclic_logGroup_of_one_free_prime {S T : Finset Nat.Primes}
    (n : Nat.Primes → ℕ) {q : Nat.Primes} (hfree : S \ T = {q}) :
    ∃ d : ℕ, 0 < d ∧ logGroup (group S T n) =
      AddSubgroup.zmultiples ((d : ℝ) * Real.log (q : ℕ)) := by
  have hn : ¬ Dense (logGroup (group S T n) : Set ℝ) :=
    not_dense_logGroup_of_card_le_one n (by rw [hfree, Finset.card_singleton])
  obtain ⟨a, ha⟩ := (logGroup (group S T n)).dense_or_cyclic.resolve_left hn
  have heq : logGroup (group S T n) = AddSubgroup.zmultiples a :=
    ha.trans (AddSubgroup.zmultiples_eq_closure a).symm
  have hsub : group S T n ≤ supported {q} := by
    rw [delete_local_support S T n, hfree]
    exact inf_le_left
  have ha_mem : a ∈ logGroup (group S T n) := by
    rw [heq]
    exact AddSubgroup.mem_zmultiples a
  obtain ⟨z, hz⟩ := logGroup_le_of_supported_singleton hsub ha_mem
  change z • Real.log (q : ℕ) = a at hz
  have hlog : 0 < Real.log (q : ℕ) := Real.log_pos (by exact_mod_cast q.2.one_lt)
  have hq : q ∈ S \ T := by rw [hfree]; exact mem_singleton_self q
  have hdis : Disjoint ({q} : Finset Nat.Primes) T :=
    disjoint_singleton_left.mpr (mem_sdiff.mp hq).2
  obtain ⟨M, hM, hm⟩ := common_supported_power {q} T n hdis
  have hMmem : (M : ℝ) * Real.log (q : ℕ) ∈ logGroup (group S T n) := by
    let u : group S T n := ⟨primeUnit q ^ M, by
      rw [delete_local_support S T n, hfree]
      exact hm ⟨primeUnit q, prime_mem_supported (mem_singleton_self q)⟩⟩
    refine ⟨u, ?_⟩
    simpa only [u, zpow_natCast, Int.cast_natCast, logPos_primeUnit]
      using logPos_zpow (primeUnit q) (M : ℤ)
  have ha0 : a ≠ 0 := by
    intro hzero
    rw [heq, hzero, AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] at hMmem
    exact (mul_pos (Nat.cast_pos.mpr hM) hlog).ne' hMmem
  have hz0 : z ≠ 0 := by
    intro hzero
    apply ha0
    rw [← hz, hzero, zero_zsmul]
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz0, ?_⟩
  have habs : |a| = (z.natAbs : ℝ) * Real.log (q : ℕ) := by
    rw [← hz, zsmul_eq_mul, abs_mul, abs_of_pos hlog]
    have hcast : |(z : ℝ)| = (z.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    rw [hcast]
  have hspan : AddSubgroup.zmultiples |a| = AddSubgroup.zmultiples a := by
    rcases le_total 0 a with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, AddSubgroup.zmultiples_neg]
  rw [← habs, hspan]
  exact heq

/-- Two free primes approximate every real logarithm despite all selected local congruences. -/
theorem log_near (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (hcard : 2 ≤ (S \ T).card) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : group S T n, |logPos (u : posUnits) - t| < ε := by
  obtain ⟨q, hq, r, hr, hqr⟩ := two_free_primes hcard
  exact log_near_of_two_free_primes n hq hr hqr t hε

/-- Every mass-zero Weil negative square survives on the dense principal S-unit group. -/
theorem polarIndex_full (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (hcard : 2 ≤ (S \ T).card) :
    polarIndex (ratCorr ∘ (group S T n).subtype) = negIndex ratCorr :=
  polarIndex_ratCorr_of_dense_log _ (log_near S T n hcard)

/-- The ordinary Weil negative index is also unchanged on the dense side. -/
theorem negIndex_full (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (hcard : 2 ≤ (S \ T).card) :
    negIndex (ratCorr ∘ (group S T n).subtype) = negIndex ratCorr := by
  refine le_antisymm (negIndex_comp_le ratCorr _) ?_
  rw [← polarIndex_full S T n hcard]
  exact polarIndex_le_negIndex _

/-- The restricted correlation values approximate every global correlation value. -/
theorem correlation_near (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (hcard : 2 ≤ (S \ T).card) (u : posUnits) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : group S T n, ‖ratCorr v - ratCorr u‖ < ε := by
  have hc : Continuous (fun t : ℝ => splineCorr (-t)) :=
    TowerCoupling.continuous_splineCorr.comp continuous_neg
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := logPos u)) ε hε
  obtain ⟨v, hv⟩ := log_near S T n hcard (logPos u) hδ
  refine ⟨v, ?_⟩
  simpa only [dist_eq_norm, ratCorr] using hclose (by simpa only [Real.dist_eq] using hv)

/-- A fixed positive oscillation survives every finite restriction retaining two free primes. -/
theorem uniform_correlation_oscillation :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (S T : Finset Nat.Primes) (n : Nat.Primes → ℕ),
      2 ≤ (S \ T).card → ∃ u : group S T n, ε ≤ ‖ratCorr u - ratCorr 1‖ := by
  obtain ⟨v, hv⟩ := exists_ratCorr_ne_identity
  have hpos : 0 < ‖ratCorr v - ratCorr 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
  refine ⟨‖ratCorr v - ratCorr 1‖ / 2, half_pos hpos, fun S T n hcard => ?_⟩
  obtain ⟨u, hu⟩ := correlation_near S T n hcard v (half_pos hpos)
  refine ⟨u, ?_⟩
  have htri := norm_add_le (ratCorr v - ratCorr u) (ratCorr u - ratCorr 1)
  rw [sub_add_sub_cancel, norm_sub_rev (ratCorr v) (ratCorr u)] at htri
  linarith only [htri, hu]

end GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits


#print axioms GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits.delete_local_support
#print axioms GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits.dense_logGroup_iff
#print axioms GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits.cyclic_logGroup_of_one_free_prime
#print axioms GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits.negIndex_full
#print axioms GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits.uniform_correlation_oscillation
