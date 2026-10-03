import GaloisForLFunctions.RHTower.EulerDeletionPrimeCountEndpointTransfer
import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation
import GaloisForLFunctions.RHTower.SoninPrimePolarCofinalGroundEnergy

/-!
# Exact jet LCM decomposition of the native prime–polar covariance

The literal Möbius prime-count jet has complete LCM self-convolution equal
to its negative. Two incidence coordinates retain an exact Möbius/gcd
fibre law. Finite kernel transport includes all LCM labels, even those
above the physical cutoff.

Specialization to the actual Sonin ground source keeps the original polar
cell masses, all proper prime powers, both unequal cross terms and the
terminal square. These finite identities do not bound the infinite energy.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
namespace RHTower.PrimeCountDamping

/-- The literal endpoint jet is the negative of its complete LCM self-convolution. -/
theorem lcmPairFibre_jetCoeff (n : ℕ) : lcmPairFibre jetCoeff n = -jetCoeff n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [lcmPairFibre, jetCoeff]
  rw [← lcmPairFibre_moebius_inversion jetCoeff n hn,
    jetCoeff_eq_primePower_convolution hn.ne', neg_neg]
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y =>
    ((moebius x : ℤ) : ℝ) * (divisorFibrePrefix jetCoeff y)^2)]
  apply sum_congr rfl
  intro q hq
  have hq0 : q ≠ 0 := (Nat.pos_of_mem_divisors hq).ne'
  rw [divisorFibrePrefix, sum_divisors_jet hq0]
  split_ifs <;> ring

/-- Complete LCM fibre of the literal jet at two incidence coordinates. -/
def jetLcmIncidence (n k m : ℕ) : ℝ :=
  finiteLcmPairCrossFibre n.divisors
    (fun d => if d ∣ k then jetCoeff d else 0)
    (fun e => if e ∣ m then jetCoeff e else 0) n

private theorem restricted_jet_prefix {n r : ℕ} (hrn : r ∣ n) (hn : n ≠ 0) (k : ℕ) :
    finiteDivisorFibrePrefix n.divisors (fun d => if d ∣ k then jetCoeff d else 0) r =
      if IsPrimePow (Nat.gcd r k) then -1 else 0 := by
  have hr : r ≠ 0 := ne_zero_of_dvd_ne_zero hn hrn
  have hg : Nat.gcd r k ≠ 0 := by positivity
  unfold finiteDivisorFibrePrefix
  rw [← Finset.sum_filter]
  have he : (n.divisors.filter (fun d => d ∣ r)).filter (fun d => d ∣ k) =
      (Nat.gcd r k).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨_,_⟩,hdr⟩,hdk⟩
      exact ⟨Nat.dvd_gcd hdr hdk,hg⟩
    · rintro ⟨hdg,_⟩
      have hdr := hdg.trans (Nat.gcd_dvd_left r k)
      exact ⟨⟨⟨hdr.trans hrn,hn⟩,hdr⟩,hdg.trans (Nat.gcd_dvd_right r k)⟩
  rw [he, sum_divisors_jet hg]

/-- Exact signed two-coordinate jet fibre. No period average or absolute value is taken. -/
theorem jetLcmIncidence_eq_moebius_gcd (n k m : ℕ) :
    jetLcmIncidence n k m = ∑ r ∈ n.divisors,
      (moebius (n/r):ℝ) *
        ((if IsPrimePow (Nat.gcd r k) then 1 else 0) *
          (if IsPrimePow (Nat.gcd r m) then 1 else 0)) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [jetLcmIncidence, finiteLcmPairCrossFibre]
  rw [jetLcmIncidence, ← finiteLcmPairCrossFibre_moebius_inversion _ _ _ n hn]
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (moebius x:ℝ) *
    (finiteDivisorFibrePrefix n.divisors (fun d => if d ∣ k then jetCoeff d else 0) y *
      finiteDivisorFibrePrefix n.divisors (fun d => if d ∣ m then jetCoeff d else 0) y))]
  apply sum_congr rfl
  intro r hr
  rw [restricted_jet_prefix (Nat.dvd_of_mem_divisors hr) hn.ne' k,
    restricted_jet_prefix (Nat.dvd_of_mem_divisors hr) hn.ne' m]
  split_ifs <;> ring

/-- On equal incidence coordinates, the entire complete fibre has the opposite jet sign. -/
theorem jetLcmIncidence_diagonal (n k : ℕ) :
    jetLcmIncidence n k k = if n ∣ k then -jetCoeff n else 0 := by
  unfold jetLcmIncidence finiteLcmPairCrossFibre
  by_cases hnk : n ∣ k
  · rw [if_pos hnk, ← lcmPairFibre_jetCoeff, lcmPairFibre]
    apply sum_congr rfl
    intro de hde
    have hd := (mem_product.mp (mem_filter.mp hde).1).1
    have he := (mem_product.mp (mem_filter.mp hde).1).2
    simp [if_pos ((Nat.dvd_of_mem_divisors hd).trans hnk),
      if_pos ((Nat.dvd_of_mem_divisors he).trans hnk)]
  · rw [if_neg hnk]
    apply sum_eq_zero
    intro de hde
    have hl := (mem_filter.mp hde).2
    by_cases hd : de.1 ∣ k
    · have he : ¬de.2 ∣ k := fun he => hnk (hl ▸ Nat.lcm_dvd hd he)
      simp [he]
    · simp [hd]

/-- Incidence never admits a fibre outside the exact product support. -/
theorem jetLcmIncidence_eq_zero_of_not_dvd (n k m : ℕ) (h : ¬n ∣ k*m) :
    jetLcmIncidence n k m = 0 := by
  unfold jetLcmIncidence finiteLcmPairCrossFibre
  apply sum_eq_zero
  intro de hde
  have hl := (mem_filter.mp hde).2
  by_cases hd : de.1 ∣ k
  · have he : ¬de.2 ∣ m := by
      intro he
      apply h
      rw [← hl]
      exact Nat.lcm_dvd (hd.trans (dvd_mul_right k m)) (he.trans (dvd_mul_left m k))
    simp [he]
  · simp [hd]

private theorem incidence_carrier (N n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (hkN : k≤N) (hmN : m≤N) :
    finiteLcmPairCrossFibre (Icc 1 N)
      (fun d => if d ∣ k then jetCoeff d else 0)
      (fun e => if e ∣ m then jetCoeff e else 0) n = jetLcmIncidence n k m := by
  unfold finiteLcmPairCrossFibre jetLcmIncidence
  unfold finiteLcmPairCrossFibre
  have hfilter (s : Finset (ℕ × ℕ)) :
      (∑ de ∈ s, (if de.1 ∣ k then jetCoeff de.1 else 0)*
        (if de.2 ∣ m then jetCoeff de.2 else 0)) =
      ∑ de ∈ s.filter (fun de => de.1 ∣ k ∧ de.2 ∣ m), jetCoeff de.1*jetCoeff de.2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro de _
    split_ifs <;> simp_all
  rw [hfilter, hfilter]
  congr 1
  ext de
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨hd,he⟩,hl⟩,hdk,hem⟩
    have hn : n≠0 := by
      rw [← hl]
      exact Nat.lcm_ne_zero (by omega) (by omega)
    exact ⟨⟨⟨⟨hl ▸ Nat.dvd_lcm_left _ _,hn⟩,
      ⟨hl ▸ Nat.dvd_lcm_right _ _,hn⟩⟩,hl⟩,hdk,hem⟩
  · rintro ⟨⟨⟨⟨hd,hn⟩,⟨he,_⟩⟩,hl⟩,hdk,hem⟩
    have hdpos : 0 < de.1 := Nat.pos_of_dvd_of_pos hdk hk
    have hepos : 0 < de.2 := Nat.pos_of_dvd_of_pos hem hm
    exact ⟨⟨⟨⟨hdpos,(Nat.le_of_dvd hk hdk).trans hkN⟩,
      ⟨hepos,(Nat.le_of_dvd hm hem).trans hmN⟩⟩,hl⟩,hdk,hem⟩

private theorem incidence_sum (N k : ℕ) (hk : 0 < k) (hkN : k≤N) :
    (∑ d ∈ Icc 1 N, if d ∣ k then jetCoeff d else 0) =
      if IsPrimePow k then -1 else 0 := by
  rw [← sum_filter]
  have he : (Icc 1 N).filter (fun d => d ∣ k)=k.divisors := by
    ext d
    simp only [mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,hdk⟩
      exact ⟨hdk,hk.ne'⟩
    · rintro ⟨hdk,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdk hk,(Nat.le_of_dvd hk hdk).trans hkN⟩,hdk⟩
  rw [he, sum_divisors_jet hk.ne']

/-- Every finite prime-power pair splits into complete incidence fibres, including all high LCMs. -/
theorem primePower_pair_eq_jetLcm (N k m : ℕ) (hk : k ∈ Icc 1 N) (hm : m ∈ Icc 1 N) :
    (if IsPrimePow k then (1:ℝ) else 0)*(if IsPrimePow m then 1 else 0) =
      ∑ n ∈ (Icc 1 N ×ˢ Icc 1 N).image (fun de => Nat.lcm de.1 de.2),
        jetLcmIncidence n k m := by
  have h := finite_sum_mul_eq_lcmPairCrossFibres (Icc 1 N)
    (fun d => if d ∣ k then jetCoeff d else 0)
    (fun e => if e ∣ m then jetCoeff e else 0)
  rw [incidence_sum N k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2,
    incidence_sum N m (mem_Icc.mp hm).1 (mem_Icc.mp hm).2] at h
  simp_rw [incidence_carrier N _ k m (mem_Icc.mp hk).1 (mem_Icc.mp hm).1
    (mem_Icc.mp hk).2 (mem_Icc.mp hm).2] at h
  convert h using 1
  split_ifs <;> ring

/-- Full signed kernel transport. The weight can be the actual reciprocal-maximum covariance;
all cross-coordinate terms, gcd classes and LCM labels above the physical cutoff remain. -/
theorem primePower_kernel_eq_jetLcm (N : ℕ) (K : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
      K k m * ((if IsPrimePow k then (1:ℝ) else 0)*(if IsPrimePow m then 1 else 0))) =
      ∑ n ∈ (Icc 1 N ×ˢ Icc 1 N).image (fun de => Nat.lcm de.1 de.2),
        ∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 N, K k m*jetLcmIncidence n k m := by
  calc
    _ = ∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
        ∑ n ∈ (Icc 1 N ×ˢ Icc 1 N).image (fun de => Nat.lcm de.1 de.2),
          K k m*jetLcmIncidence n k m := by
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro m hm
      rw [primePower_pair_eq_jetLcm N k m hk hm, mul_sum]
    _ = ∑ k ∈ Icc 1 N,
        ∑ n ∈ (Icc 1 N ×ˢ Icc 1 N).image (fun de => Nat.lcm de.1 de.2),
          ∑ m ∈ Icc 1 N, K k m*jetLcmIncidence n k m := by
      apply sum_congr rfl
      intro k hk
      rw [sum_comm]
    _ = _ := by rw [sum_comm]

/-- Full centering keeps the prime-power pair term and both unequal cross terms. -/
theorem centered_primePower_kernel_eq_jetLcm (N : ℕ) (K : ℕ → ℕ → ℝ) (b : ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
      K k m * ((if IsPrimePow k then (1:ℝ) else 0)-b k)*
        ((if IsPrimePow m then 1 else 0)-b m)) =
      (∑ n ∈ (Icc 1 N ×ˢ Icc 1 N).image (fun de => Nat.lcm de.1 de.2),
        ∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 N, K k m*jetLcmIncidence n k m)+
      ∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
        K k m*(b k*b m-(if IsPrimePow k then 1 else 0)*b m-
          b k*(if IsPrimePow m then 1 else 0)) := by
  rw [← primePower_kernel_eq_jetLcm]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  ring

end RHTower.PrimeCountDamping

namespace RHTower
open PrimeCountDamping

/-- Exact correction from prime-power incidence to the original prime–polar coefficient.
Every proper prime power and the unchanged polar mass are retained. -/
def soninPrimePolarJetCenter (n : ℕ) : ℝ :=
  soninPolarGroundCellMass n + (if IsPrimePow (n+2) ∧ ¬(n+2).Prime then 1 else 0)

private theorem coefficient_jet_center (n : ℕ) :
    soninPrimePolarGridCoefficient n =
      (if IsPrimePow (n+2) then (1:ℝ) else 0)-soninPrimePolarJetCenter n := by
  unfold soninPrimePolarGridCoefficient soninPrimePolarJetCenter
  by_cases hp : (n+2).Prime
  · simp [hp, hp.isPrimePow]
  · by_cases hpow : IsPrimePow (n+2) <;> simp [hp,hpow]

private theorem grid_entry_inner (a : ℝ) (ha : 0≤a) (i j : ℕ) :
    inner ℂ (soninGroundEntry a (Real.log (i+2:ℝ)))
      (soninGroundEntry a (Real.log (j+2:ℝ))) =
      ((2*a/(max (i+2) (j+2):ℕ):ℝ):ℂ) := by
  wlog hij : i≤j generalizing i j
  · rw [← inner_conj_symm, this j i (by omega), Complex.conj_ofReal, max_comm]
  have hi : (0:ℝ)<(i:ℝ)+2 := by positivity
  have hj : (0:ℝ)<(j:ℝ)+2 := by positivity
  have hl : Real.log (i+2:ℝ)≤Real.log (j+2:ℝ) :=
    Real.log_le_log hi (by exact_mod_cast Nat.add_le_add_right hij 2)
  rw [inner_soninGroundEntry_of_le a ha _ _ hl, Real.exp_neg, Real.exp_log hj,
    max_eq_right (Nat.add_le_add_right hij 2)]
  push_cast
  simp only [div_eq_mul_inv]

/-- The literal grid norm retains the full reciprocal-maximum covariance. -/
theorem soninPrimePolarGridSource_norm_sq_covariance (a : ℝ) (ha : 0≤a) (N : ℕ) :
    ‖soninPrimePolarGridSource a N‖^2 = 2*a*
      ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
        (1/(max (i+2) (j+2):ℕ):ℝ)*
          soninPrimePolarGridCoefficient i*soninPrimePolarGridCoefficient j := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), soninPrimePolarGridSource, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, grid_entry_inner a ha]
  simp only [map_sum, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  change soninPrimePolarGridCoefficient i *
    (soninPrimePolarGridCoefficient j * (2*a/(max (i+2) (j+2):ℕ))) = _
  ring

private theorem range_pair (N i j : ℕ) (hi : i∈range (N+1)) (hj : j∈range (N+1)) :
    (if IsPrimePow (i+2) then (1:ℝ) else 0)*(if IsPrimePow (j+2) then 1 else 0) =
      ∑ n ∈ (Icc 1 (N+2) ×ˢ Icc 1 (N+2)).image (fun de => Nat.lcm de.1 de.2),
        jetLcmIncidence n (i+2) (j+2) := by
  apply primePower_pair_eq_jetLcm
  · simp only [mem_Icc]
    have := mem_range.mp hi
    omega
  · simp only [mem_Icc]
    have := mem_range.mp hj
    omega

/-- Complete LCM decomposition of the actual TG covariance, with the original polar
cross terms and every proper-prime-power correction kept outside the fibre sum. -/
theorem soninPrimePolarGrid_covariance_eq_jetLcm (N : ℕ) :
    (∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
      (1/(max (i+2) (j+2):ℕ):ℝ)*
        soninPrimePolarGridCoefficient i*soninPrimePolarGridCoefficient j) =
      (∑ n ∈ (Icc 1 (N+2) ×ˢ Icc 1 (N+2)).image (fun de => Nat.lcm de.1 de.2),
        ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
          (1/(max (i+2) (j+2):ℕ):ℝ)*jetLcmIncidence n (i+2) (j+2))+
      ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
        (1/(max (i+2) (j+2):ℕ):ℝ)*
          (soninPrimePolarJetCenter i*soninPrimePolarJetCenter j-
            (if IsPrimePow (i+2) then 1 else 0)*soninPrimePolarJetCenter j-
            soninPrimePolarJetCenter i*(if IsPrimePow (j+2) then 1 else 0)) := by
  have hp :
      (∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
        (1/(max (i+2) (j+2):ℕ):ℝ)*
          ((if IsPrimePow (i+2) then (1:ℝ) else 0)*(if IsPrimePow (j+2) then 1 else 0))) =
      ∑ n ∈ (Icc 1 (N+2) ×ˢ Icc 1 (N+2)).image (fun de => Nat.lcm de.1 de.2),
        ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
          (1/(max (i+2) (j+2):ℕ):ℝ)*jetLcmIncidence n (i+2) (j+2) := by
    calc
      _ = ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
          ∑ n ∈ (Icc 1 (N+2) ×ˢ Icc 1 (N+2)).image (fun de => Nat.lcm de.1 de.2),
            (1/(max (i+2) (j+2):ℕ):ℝ)*jetLcmIncidence n (i+2) (j+2) := by
        apply sum_congr rfl
        intro i hi
        apply sum_congr rfl
        intro j hj
        rw [range_pair N i j hi hj, mul_sum]
      _ = ∑ i ∈ range (N+1),
          ∑ n ∈ (Icc 1 (N+2) ×ˢ Icc 1 (N+2)).image (fun de => Nat.lcm de.1 de.2),
            ∑ j ∈ range (N+1), (1/(max (i+2) (j+2):ℕ):ℝ)*jetLcmIncidence n (i+2) (j+2) := by
        apply sum_congr rfl
        intro i hi
        rw [sum_comm]
      _ = _ := by rw [sum_comm]
  rw [← hp, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  rw [coefficient_jet_center, coefficient_jet_center]
  ring

/-- Exact equality between positive cumulative-plus-terminal energy and the full signed kernel. -/
theorem soninPrimePolarGrid_energy_eq_covariance (N : ℕ) :
    (∑ n ∈ range (N+1), soninPrimePolarGridEnergy n)+
      soninPrimePolarGridCumulative N^2/(N+3:ℝ) =
      ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
        (1/(max (i+2) (j+2):ℕ):ℝ)*
          soninPrimePolarGridCoefficient i*soninPrimePolarGridCoefficient j := by
  have h := (soninPrimePolarGridSource_norm_sq 1 (by norm_num) N).symm.trans
    (soninPrimePolarGridSource_norm_sq_covariance 1 (by norm_num) N)
  linarith

end RHTower
