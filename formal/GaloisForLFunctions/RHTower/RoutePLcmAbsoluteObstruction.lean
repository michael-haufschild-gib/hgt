import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absolute variation of the unpaid RP LCM fibres

The physical cutoff removes the product of two late primes. Its complete LCM
fibre therefore consists of the two ordered prime pairs. These entire fibres
force a lower bound by late-prime mass squared, less the paid diagonal.
The signed sum over different fibres is retained in the RP problem.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter
open scoped Topology

namespace RHTower

private theorem clipped_semiprime_pair {M p q d e : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hM : M < p * q) (hd : d ≤ M) (he : e ≤ M)
    (hl : Nat.lcm d e = p * q) :
    (d = p ∧ e = q) ∨ (d = q ∧ e = p) := by
  have hdivs : (p * q).divisors = ({1, p, q, p * q} : Finset ℕ) := by
    ext n
    simp [Nat.divisors_mul, hp.divisors, hq.divisors, Finset.mem_mul, mul_comm]
    tauto
  have hd' : d ∈ (p * q).divisors := Nat.mem_divisors.mpr
    ⟨hl ▸ Nat.dvd_lcm_left d e, Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have he' : e ∈ (p * q).divisors := Nat.mem_divisors.mpr
    ⟨hl ▸ Nat.dvd_lcm_right d e, Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  rw [hdivs] at hd' he'
  simp only [mem_insert, mem_singleton] at hd' he'
  rcases hd' with rfl | rfl | rfl | rfl <;>
    rcases he' with rfl | rfl | rfl | rfl
  all_goals try simp only [Nat.lcm_one_left, Nat.lcm_one_right, Nat.lcm_self] at hl
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩ | omega

/-- The complete physical semiprime fibre contains precisely two terms when
both primes are active and their product is beyond the cutoff. -/
theorem finiteLcmPairFibre_clipped_semiprime {M p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hM : M < p * q) (a : ℕ → ℝ) :
    finiteLcmPairFibre (Icc 1 M) a (p * q) = 2 * a p * a q := by
  have hcop := (Nat.coprime_primes hp hq).mpr hne
  have hs : (Icc 1 M ×ˢ Icc 1 M).filter (fun de => Nat.lcm de.1 de.2 = p*q) =
      {(p,q), (q,p)} := by
    ext de
    constructor
    · intro h
      obtain ⟨hde, hl⟩ := mem_filter.mp h
      obtain ⟨hd, he⟩ := mem_product.mp hde
      rcases clipped_semiprime_pair hp hq hne hM (mem_Icc.mp hd).2
        (mem_Icc.mp he).2 hl with ⟨hd,he⟩ | ⟨hd,he⟩ <;>
        simp [hd, he, Prod.ext_iff]
    · intro h
      simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl <;>
        simp [hp.one_lt.le, hq.one_lt.le, hpM, hqM, hcop.lcm_eq_mul, Nat.lcm_comm]
  rw [finiteLcmPairFibre, hs]
  simp [Prod.ext_iff, hne, hne.symm, mul_comm]
  ring

/-- Absolute values are taken after summing every active pair in each LCM fibre. -/
def routePHighLcmVariation (M : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 M ×ˢ Icc 1 M).image (fun de => Nat.lcm de.1 de.2),
    if M < k then |finiteLcmPairFibre (Icc 1 M) (mobiusDivisorDilationChannel M) k| else 0

private def latePrimePairs (M : ℕ) : Finset (ℕ × ℕ) :=
  ((GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M) ×ˢ
    (GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M)).filter (fun de => de.1 ≠ de.2)

private theorem latePrimePairs_subset (M : ℕ) :
    latePrimePairs M ⊆ Icc 1 M ×ˢ Icc 1 M := by
  intro de hde
  obtain ⟨hde, _⟩ := mem_filter.mp hde
  obtain ⟨hp, hq⟩ := mem_product.mp hde
  obtain ⟨hp, _, hpM⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  obtain ⟨hq, _, hqM⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hq
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨hp.one_lt.le, hpM⟩,
    mem_Icc.mpr ⟨hq.one_lt.le, hqM⟩⟩

private theorem latePrimePairs_lcm_gt {M : ℕ} {de : ℕ × ℕ}
    (hde : de ∈ latePrimePairs M) : M < Nat.lcm de.1 de.2 := by
  obtain ⟨hmem, hne⟩ := mem_filter.mp hde
  obtain ⟨hpL, hqL⟩ := mem_product.mp hmem
  obtain ⟨hp, _, _⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hpL
  obtain ⟨hq, hqlo, _⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hqL
  rw [((Nat.coprime_primes hp hq).mpr hne).lcm_eq_mul]
  have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp hqlo
  nlinarith [hp.two_le]

private theorem latePrimePairs_fibre_complete {M k : ℕ}
    (hk : ((latePrimePairs M).filter (fun de => Nat.lcm de.1 de.2 = k)).Nonempty) :
    (latePrimePairs M).filter (fun de => Nat.lcm de.1 de.2 = k) =
      (Icc 1 M ×ˢ Icc 1 M).filter (fun de => Nat.lcm de.1 de.2 = k) := by
  obtain ⟨pq, hpq⟩ := hk
  obtain ⟨hpqmem, hpqk⟩ := mem_filter.mp hpq
  have hkgt := latePrimePairs_lcm_gt hpqmem
  obtain ⟨hmem, hne⟩ := mem_filter.mp hpqmem
  obtain ⟨hpL, hqL⟩ := mem_product.mp hmem
  obtain ⟨hp, _, _⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hpL
  obtain ⟨hq, _, _⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hqL
  have hprod := ((Nat.coprime_primes hp hq).mpr hne).lcm_eq_mul
  rw [hprod] at hpqk hkgt
  ext de
  constructor
  · intro h
    obtain ⟨hmem, hl⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨latePrimePairs_subset M hmem, hl⟩
  · intro h
    obtain ⟨hmem, hl⟩ := mem_filter.mp h
    obtain ⟨hd, he⟩ := mem_product.mp hmem
    have hl' : Nat.lcm de.1 de.2 = pq.1 * pq.2 := hl.trans hpqk.symm
    rcases clipped_semiprime_pair hp hq hne hkgt (mem_Icc.mp hd).2
      (mem_Icc.mp he).2 hl' with ⟨hd,he⟩ | ⟨hd,he⟩ <;>
      apply mem_filter.mpr <;> refine ⟨?_, hl⟩ <;>
      simp [latePrimePairs, hd, he, hpL, hqL, hne, hne.symm]

private theorem latePrimePairs_sum_le_variation (M : ℕ) :
    (∑ de ∈ latePrimePairs M,
      mobiusDivisorDilationChannel M de.1 * mobiusDivisorDilationChannel M de.2) ≤
      routePHighLcmVariation M := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := latePrimePairs M)
    (t := (Icc 1 M ×ˢ Icc 1 M).image (fun de => Nat.lcm de.1 de.2))
    (g := fun de => Nat.lcm de.1 de.2)
    (fun de hde => mem_image_of_mem _ (latePrimePairs_subset M hde))]
  apply sum_le_sum
  intro k _
  by_cases hk : ((latePrimePairs M).filter (fun de => Nat.lcm de.1 de.2 = k)).Nonempty
  · have hcomplete := latePrimePairs_fibre_complete hk
    obtain ⟨de, hde⟩ := hk
    obtain ⟨hmem, hl⟩ := mem_filter.mp hde
    have hkgt : M < k := hl ▸ latePrimePairs_lcm_gt hmem
    rw [if_pos hkgt, hcomplete]
    exact le_abs_self _
  · rw [not_nonempty_iff_eq_empty.mp hk, sum_empty]
    split_ifs <;> positivity

private theorem latePrimePairs_sum_eq (M : ℕ) :
    (∑ de ∈ latePrimePairs M,
      mobiusDivisorDilationChannel M de.1 * mobiusDivisorDilationChannel M de.2) =
      mobiusDivisorLatePrimeMass M ^ 2 -
        ∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M,
          mobiusDivisorDilationChannel M p ^ 2 := by
  let L := GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M
  let a := mobiusDivisorDilationChannel M
  have hsum : (∑ p ∈ L, a p) = -mobiusDivisorLatePrimeMass M := by
    rw [mobiusDivisorLatePrimeMass, ← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    have hp' := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).1
    simp [a, mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime hp']
  have hsplit : (∑ de ∈ latePrimePairs M, a de.1 * a de.2) +
      (∑ p ∈ L, a p ^ 2) = (∑ p ∈ L, a p)^2 := by
    rw [latePrimePairs, sum_filter, sum_product, sq, sum_mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    change p ∈ L at hp
    have hdiag : (∑ q ∈ L, if p = q then a p * a q else 0) = a p ^ 2 := by
      simp [hp, sq]
    rw [← hdiag, ← sum_add_distrib]
    apply sum_congr rfl
    intro q _
    by_cases h : p = q <;> simp [h]
  rw [hsum, neg_sq] at hsplit
  linarith only [hsplit]

/-- Entire high-LCM fibres carry at least late-prime mass squared, minus a
quadratic diagonal. Cancellation within each fibre cannot remove this mass. -/
theorem routePHighLcmVariation_ge_latePrimeMass (M : ℕ) :
    mobiusDivisorLatePrimeMass M ^ 2 - 722 * (M : ℝ)^2 ≤ routePHighLcmVariation M := by
  have hd : (∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M,
      mobiusDivisorDilationChannel M p ^ 2) ≤ 722 * (M : ℝ)^2 := by
    refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)).trans
      (sum_mobiusDivisorDilationChannel_sq_le_quadratic M)
    intro p hp
    obtain ⟨hp, _, hpM⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    exact mem_Icc.mpr ⟨hp.one_lt.le, hpM⟩
  have h := latePrimePairs_sum_le_variation M
  rw [latePrimePairs_sum_eq] at h
  linarith only [hd, h]

private theorem log_double_div_fourth_root_zero :
    Tendsto (fun N : ℕ => Real.log (2*(N:ℝ))/Real.sqrt (Real.sqrt N)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^(1/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log 2/(N:ℝ)^(1/4:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      hpow.inv_tendsto_atTop.const_mul (Real.log 2)
  have hl : Tendsto (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)^(1/4:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/4)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  apply (show Tendsto (fun N : ℕ => Real.log 2/(N:ℝ)^(1/4:ℝ) +
      Real.log (N:ℝ)/(N:ℝ)^(1/4:ℝ)) atTop (𝓝 0) from by simpa using hc.add hl).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hr : Real.sqrt (Real.sqrt N) = (N:ℝ)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg (α:=ℝ) N)]
    norm_num
  rw [hr, Real.log_mul (by norm_num) (by exact_mod_cast (show N ≠ 0 by omega))]
  ring

/-- A harmonic floor survives absolute values of complete LCM fibres at the
critical damped exponent `7/2`. This uses the actual prime-channel mass. -/
theorem eventually_routePHighLcmVariation_critical_floor :
    ∀ᶠ N : ℕ in atTop,
      1 / (4*(N:ℝ)) ≤ routePHighLcmVariation (4*N) /
        (((4*N:ℕ):ℝ)^3 * Real.sqrt (4*N:ℕ)) := by
  have hlog := log_double_div_fourth_root_zero.eventually_le_const
    (by norm_num : (0:ℝ)<1/1280)
  have hsqrt : ∀ᶠ N : ℕ in atTop, (722:ℝ) ≤ Real.sqrt N :=
    ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 722)
  filter_upwards [hlog, hsqrt, eventually_mobiusDivisorLatePrimeMass_ge,
    eventually_ge_atTop (1:ℕ)] with N hl hs hmass hN
  have hNr : (0:ℝ)<N := by positivity
  have hroot : 0 < Real.sqrt (Real.sqrt N) := by positivity
  have hlogpos : 0 < Real.log (2*(N:ℝ)) := Real.log_pos (by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  have hl' : 1280 * Real.log (2*(N:ℝ)) ≤ Real.sqrt (Real.sqrt N) := by
    have h := (div_le_iff₀ hroot).mp hl
    linarith
  have hmass' : 16*(N:ℝ)*Real.sqrt (Real.sqrt N) ≤ mobiusDivisorLatePrimeMass (4*N) := by
    refine le_trans ((le_div_iff₀ (show 0 < 80*Real.log (2*(N:ℝ)) by positivity)).mpr ?_) hmass
    calc
      _ = ((N:ℝ)*Real.sqrt (Real.sqrt N)) * (1280*Real.log (2*(N:ℝ))) := by ring
      _ ≤ ((N:ℝ)*Real.sqrt (Real.sqrt N)) * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hl' (by positivity)
      _ = (N:ℝ)*Real.sqrt N := by nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (N:ℝ))]
  have hsq : (16*(N:ℝ)*Real.sqrt (Real.sqrt N))^2 ≤ mobiusDivisorLatePrimeMass (4*N)^2 := by
    have hpos : 0 ≤ 16*(N:ℝ)*Real.sqrt (Real.sqrt N) := by positivity
    nlinarith
  have hsq' : (16*(N:ℝ)*Real.sqrt (Real.sqrt N))^2 = 256*(N:ℝ)^2*Real.sqrt N := by
    rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg (N:ℝ))]
    ring
  rw [hsq'] at hsq
  have hdiag : 11552*(N:ℝ)^2 ≤ 224*(N:ℝ)^2*Real.sqrt N := by
    have h := mul_le_mul_of_nonneg_left hs (sq_nonneg (N:ℝ))
    nlinarith [sq_nonneg (N:ℝ)]
  have hv := routePHighLcmVariation_ge_latePrimeMass (4*N)
  push_cast at hv
  have hfloor : 32*(N:ℝ)^2*Real.sqrt N ≤ routePHighLcmVariation (4*N) := by
    nlinarith only [hv, hsq, hdiag]
  calc
    1/(4*(N:ℝ)) = (32*(N:ℝ)^2*Real.sqrt N) /
        (((4*N:ℕ):ℝ)^3 * Real.sqrt (4*N:ℕ)) := by
      push_cast
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hfloor (by positivity)

/-- Absolute admission fails even after complete LCM-fibre regrouping, at a
strictly positive critical damping. This says nothing against admission of
the signed sum over different fibres. -/
theorem not_summable_routePHighLcmVariation_critical :
    ¬ Summable (fun N : ℕ => routePHighLcmVariation (4*N) /
      (((4*N:ℕ):ℝ)^3 * Real.sqrt (4*N:ℕ))) := by
  intro h
  have hh : Summable (fun N : ℕ => 1/(4*(N:ℝ))) :=
    h.of_norm_bounded_eventually_nat (by
      filter_upwards [eventually_routePHighLcmVariation_critical_floor] with N hN
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(4*(N:ℝ)))] using hN)
  apply Real.not_summable_one_div_natCast
  have hscaled : Summable (fun N : ℕ => 4*(1/(4*(N:ℝ)))) := hh.mul_left 4
  have heq : (fun N : ℕ => 4*(1/(4*(N:ℝ)))) = fun N : ℕ => 1/(N:ℝ) := by
    funext N
    ring
  rw [heq] at hscaled
  exact hscaled

end RHTower
