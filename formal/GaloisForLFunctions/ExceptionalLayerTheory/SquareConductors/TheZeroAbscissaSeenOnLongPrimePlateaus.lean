import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeListsInsideAHalfOrderObservation
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSignedSamplingOfOrdinaryPrimeCofactorIntervals

/-!
# The zero abscissa on locally constant ordinary-prime observations

Any mesh with gaps of order n^δ retains every upper midpoint exponent
strictly above δ. For each prescribed plateau length, one arithmetic
progression has bounded gaps and constant observations for that length.
Restricting all measurements to those plateaus preserves the zero abscissa.
-/

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- A sample of zero represents the initial gap before the first
positive sample. At zero the ordinary midpoint price vanishes. -/
def midpointMesh (S : Set ℕ) (δ : ℝ) := ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0<n →
  ∃ m ≤ n, (m=0 ∨ m∈S) ∧ (n:ℝ)-m ≤ K*(n:ℝ)^δ

/-- The logarithm charged to each crossed integer is absorbed in the
strict difference between the price exponent and the mesh exponent. -/
theorem midpoint_bound_from_mesh {S : Set ℕ} {δ t : ℝ} (hm : midpointMesh S δ)
    (ht : 0<t) (hδ : δ<t)
    (h : ∃ C : ℝ, ∀ n ∈ S, 0<n → primeMidpointPrice n ≤ C*(n:ℝ)^t) :
    ∃ C : ℝ, ∀ n : ℕ, 0<n → primeMidpointPrice n ≤ C*(n:ℝ)^t := by
  obtain ⟨K,hK,hmesh⟩ := hm
  obtain ⟨C,hC⟩ := h
  let ε := t-δ
  have hε : 0<ε := sub_pos.mpr hδ
  refine ⟨|C|+6*K*(4:ℝ)^ε/ε,?_⟩
  intro n hn
  obtain ⟨m,hm',hs,hgap⟩ := hmesh n hn
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hprice : primeMidpointPrice m ≤ |C| * (n:ℝ)^t := by
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · simpa [primeMidpointPrice] using mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hn'.le t)
    · exact (hC m (hs.resolve_left hp.ne') hp).trans (mul_le_mul (le_abs_self _)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hm') ht.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _))
  have hlog := Real.log_le_rpow_div (x:=((4*n:ℕ):ℝ)) (Nat.cast_nonneg _) hε
  simp only [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : 0≤(4:ℝ)) hn'.le] at hlog
  have hmotion := (le_abs_self _).trans (full_midpoint_motion hm')
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hgap (by norm_num : (0:ℝ)≤6)) hlog
    (Real.log_natCast_nonneg (4*n)) (by positivity)
  have he : (n:ℝ)^δ*(n:ℝ)^ε=(n:ℝ)^t := by
    rw [←Real.rpow_add hn',show δ+ε=t by dsimp only [ε]; ring]
  have hid : 6*(K*(n:ℝ)^δ)*((4:ℝ)^ε*(n:ℝ)^ε/ε)=
      (6*K*(4:ℝ)^ε/ε)*(n:ℝ)^t := by rw [←he]; ring
  rw [hid] at hprod
  linarith only [hmotion,hprice,hprod]

theorem prime_plateau_progression_mesh (L : ℕ) :
    midpointMesh (Set.range (primePlateauStart 4 L)) 0 := by
  let F := primePlateauStride 4 L
  have hF : 0<F := Nat.factorial_pos _
  refine ⟨((F+2:ℕ):ℝ),Nat.cast_nonneg _,?_⟩
  intro n hn
  rw [Real.rpow_zero,mul_one]
  by_cases hs : n<F+2
  · exact ⟨0,Nat.zero_le _,Or.inl rfl,by simpa only [Nat.cast_zero,sub_zero] using Nat.cast_le.mpr hs.le⟩
  let a := n-2
  let q := a/F
  have hq : 0<q := Nat.div_pos (by dsimp only [a]; omega) hF
  have hmod := Nat.mod_lt a hF
  have hdiv := Nat.mod_add_div a F
  have hn' : n=a+2 := by dsimp only [a]; omega
  have hz : primePlateauStart 4 L (q-1)=F*q+2 := by
    change F*(q-1+1)+2=_
    rw [Nat.sub_add_cancel (by omega)]
  refine ⟨F*q+2,by change a%F+F*q=a at hdiv; omega,Or.inr ⟨q-1,hz⟩,?_⟩
  change a%F+F*q=a at hdiv
  have hnat : n ≤ (F+2)+(F*q+2) := by omega
  exact sub_le_iff_le_add.mpr (by exact_mod_cast hnat)

/-- A single progression of starts of length-L plateaus carries the
entire upper prime-midpoint spectrum down to the critical line. -/
theorem zero_abscissa_iff_prime_plateau_starts {b : ℝ} (hb : 1/2 ≤ b) (L : ℕ) :
    _root_.RHTower.zetaZeroAbscissa ≤ b ↔ ∀ t : ℝ, b<t → t<1 → ∃ C : ℝ, ∀ q : ℕ,
      halfOrderMidpointRead (primePlateauStart 4 L q) ≤ C*(primePlateauStart 4 L q:ℝ)^t := by
  rw [←prime_midpoint_upper_spectrum_iff hb]
  simp only [halfOrderMidpointRead_price]
  constructor
  · intro h t ht ht'
    obtain ⟨C,hC⟩ := h t ht ht'
    exact ⟨C,fun q => hC _ (by unfold primePlateauStart; omega)⟩
  · intro h t ht ht'
    obtain ⟨C,hC⟩ := h t ht ht'
    have hpos : 0<t := by linarith only [hb,ht]
    apply midpoint_bound_from_mesh (prime_plateau_progression_mesh L) hpos hpos
    exact ⟨C,fun _ ⟨q,hq⟩ _ => hq ▸ hC q⟩

/-- It suffices to bound only measurements that stay exactly constant
through the next L integer steps. This holds for every fixed L. -/
theorem riemannHypothesis_iff_locally_constant_prime_readings (L : ℕ) :
    RiemannHypothesis ↔ ∀ t : ℝ, 1/2<t → t<1 → ∃ C : ℝ, ∀ n : ℕ, 0<n →
      (∀ j ≤ L, halfOrderMidpointRead (n+j)=halfOrderMidpointRead n) →
      halfOrderMidpointRead n ≤ C*(n:ℝ)^t := by
  constructor
  · intro h t ht ht'
    obtain ⟨C,hC⟩ := riemannHypothesis_iff_prime_midpoint.mp h t ht ht'
    exact ⟨C,fun n hn _ => (halfOrderMidpointRead_price n).symm ▸ hC n hn⟩
  · intro h
    apply riemannHypothesis_iff_prime_midpoint.mpr
    apply (prime_midpoint_upper_spectrum_iff le_rfl).mpr
    apply (zero_abscissa_iff_prime_plateau_starts le_rfl L).mpr
    intro t ht ht'
    obtain ⟨C,hC⟩ := h t ht ht'
    exact ⟨C,fun q => hC _ (by unfold primePlateauStart; omega) (half_order_prime_plateau L q).2⟩

/-- The integer part of log(n−2)/(16 log 4), less two endpoint steps. -/
def intrinsicPrimePlateauLength (n : ℕ) := midpointSieveLevel (n-2)/4-2

def logarithmicPrimePlateaus : Set ℕ := {n | ∀ j ≤ intrinsicPrimePlateauLength n,
  halfOrderMidpointRead (n+j)=halfOrderMidpointRead n}

/-- Shifting an intrinsic primorial center by two produces a logarithmic
interval of constant observations. Each possible new integer has a small
prime divisor already present in the center. -/
theorem shifted_primorial_prime_plateau {m : ℕ} (hm : 0 < m)
    (hs : primorial (midpointSieveLevel m) ∣ m) : m+2 ∈ logarithmicPrimePlateaus := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hp
  · rw [Nat.add_zero]
  apply halfOrderMidpointRead_eq_of_frozen_thresholds
  intro k hk hk' p
  have hlen : j ≤ midpointSieveLevel m/4-2 := by
    simpa only [intrinsicPrimePlateauLength,Nat.add_sub_cancel] using hj
  apply prime_plateau_of_shared_divisors (d:=4) (L:=j) hm _ le_rfl hk hk' p
  intro r hr hr'
  have hsmall : r ≤ midpointSieveLevel m := by omega
  have hq := Nat.minFac_prime (by omega : r≠1)
  exact ⟨r.minFac,hq.one_lt,Nat.minFac_dvd _,(hq.dvd_primorial_iff.mpr
    ((Nat.minFac_le (by omega)).trans hsmall)).trans hs⟩

/-- Every large integer lies at most its fourth root past the start of
a logarithmically long flat interval. -/
theorem nearby_logarithmic_prime_plateau {n : ℕ} (hn : 3<n) :
    ∃ s ≤ n, 0 < s ∧ s∈logarithmicPrimePlateaus ∧ (n:ℝ)-s ≤ (n:ℝ)^(1/4:ℝ) := by
  obtain ⟨m,hm,hmn,hdiv,hgap⟩ := nearby_primorial_midpoint (by omega : 1<n-2)
  refine ⟨m+2,by omega,by omega,shifted_primorial_prime_plateau (by omega) hdiv,?_⟩
  have hmono := Real.rpow_le_rpow (Nat.cast_nonneg (n-2)) (Nat.cast_le.mpr (Nat.sub_le n 2))
    (by norm_num : (0:ℝ)≤1/4)
  rw [Nat.cast_sub (by omega : 2≤n),Nat.cast_ofNat] at hgap hmono
  push_cast
  linarith only [hgap,hmono]

/-- The original zero-abscissa test survives even when the required
number of equal following measurements grows logarithmically in n. -/
theorem zero_abscissa_iff_logarithmic_prime_plateaus {b : ℝ} (hb : 1/2 ≤ b) :
    _root_.RHTower.zetaZeroAbscissa ≤ b ↔ ∀ t : ℝ, b<t → t<1 → ∃ C : ℝ,
      ∀ n ∈ logarithmicPrimePlateaus, 0<n → halfOrderMidpointRead n ≤ C*(n:ℝ)^t := by
  rw [←prime_midpoint_upper_spectrum_iff hb]
  simp only [halfOrderMidpointRead_price]
  constructor
  · intro h t ht ht'
    obtain ⟨C,hC⟩ := h t ht ht'
    exact ⟨C,fun n _ hn => hC n hn⟩
  · have hmesh : midpointMesh logarithmicPrimePlateaus (1/4) := by
      refine ⟨3,by norm_num,?_⟩
      intro n hn
      have h1 := Real.one_le_rpow (Nat.one_le_cast.mpr hn) (by norm_num : (0:ℝ)≤1/4)
      by_cases h : 3<n
      · obtain ⟨s,hs,_,hflat,hgap⟩ := nearby_logarithmic_prime_plateau h
        exact ⟨s,hs,Or.inr hflat,by linarith only [hgap,h1]⟩
      · refine ⟨0,Nat.zero_le _,Or.inl rfl,?_⟩
        have h3 : (n:ℝ) ≤ 3 := by exact_mod_cast le_of_not_gt h
        rw [Nat.cast_zero,sub_zero]
        linarith only [h3,h1]
    intro h t ht ht'
    exact midpoint_bound_from_mesh hmesh (by linarith only [hb,ht]) (by linarith only [hb,ht]) (h t ht ht')

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
