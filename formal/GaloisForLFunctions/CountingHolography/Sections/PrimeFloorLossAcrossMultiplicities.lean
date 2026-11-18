import GaloisForLFunctions.CountingHolography.Sections.FractionalPartsAcrossMultiplicities
import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityPerSquareConductor
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity

/-!
# Prime floor loss across multiplicities

On the separated negative prime window the same integrated contact governs a
whole interval of multiplicities. Pairing readings a short distance apart
retains a positive proportion of the prime mass after flooring.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology AbsoluteGeometryOfSpecZ ArithmeticFunction

private def actualRow (n m k : ℕ) :=
  let a := m • successorSquareTriple n
  contactMultiplicity (packet a) (3*windowEnd ((2*n+1)^2+1)) (resolution a) k

/-- After multiplication by the square root of the lag, the error of the
actual unrounded row is at most linear in its multiplicity. -/
private theorem row_error : ∃ B : ℝ, 1 ≤ B ∧ ∀ (n : ℕ) {k : ℕ}, 0 < k →
    let b := integratedContact (successorSquareTriple n) k
    |b| * Real.sqrt k ≤ B ∧ ∀ {m : ℕ}, 0 < m →
      |actualRow n m k-b*(m:ℝ)^2| * Real.sqrt k ≤ B*m := by
  obtain ⟨C,hC,hquad⟩ := contactMultiplicity_uniform_error
  obtain ⟨A,hA,hsize⟩ := contactMultiplicity_size
  refine ⟨16*A+2*C+1,by linarith only [hA,hC],fun n {k} hk => ?_⟩
  let d := successorSquareTriple n
  let L := 3*windowEnd ((2*n+1)^2+1)
  let b := integratedContact d k
  let v := fun r => contactMultiplicity (packet d) L r k
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk : (0:ℝ)<k)
  have he {r : ℕ} (hr : 0 < r) : |v r-b| * Real.sqrt k ≤ 2*C/r :=
    (le_div_iff₀ hs).mp ((hquad _ d (successorSquareTriple_mass n) hr hk).trans_eq (by ring))
  have hmass := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2
  have hv := (le_div_iff₀ hs).mp (hsize _ d L 1 k)
  have hOne := he (r := 1) one_pos
  simp only [Nat.cast_one,div_one] at hOne
  have hb := mul_le_mul_of_nonneg_right (abs_sub_abs_le_abs_sub b (v 1)) hs.le
  rw [abs_sub_comm b (v 1),sub_mul] at hb
  change |v 1| * Real.sqrt k ≤ _ at hv
  refine ⟨by linarith only [hOne,hv,hb,mul_le_mul_of_nonneg_left hmass (zero_le_one.trans hA)],?_⟩
  intro m hm
  let r := resolution (m • d)
  have ht : (m:ℝ) ≤ r := by exact_mod_cast successorSquare_resolution_ge n m
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hr := hm.trans_le (successorSquare_resolution_ge n m)
  have hdiv : (m:ℝ)^2*(2*C/r) ≤ (2*C)*m := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (hm'.trans_le ht)).mpr
    linarith only [mul_le_mul_of_nonneg_left ht (mul_nonneg (by linarith only [hC] : 0 ≤ 2*C) hm'.le)]
  have hx : actualRow n m k = (m:ℝ)^2*v r := by
    change contactMultiplicity (packet (m • d)) L r k = _
    rw [packet_smul,contactMultiplicity_scale]
  change |actualRow n m k-b*(m:ℝ)^2| * Real.sqrt k ≤ _
  rw [hx,mul_comm b,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _),mul_assoc]
  exact (mul_le_mul_of_nonneg_left (he hr) (sq_nonneg _)).trans
    (hdiv.trans (mul_le_mul_of_nonneg_right (by linarith only [hA]) hm'.le))

/-- A fixed fraction of the prime-window mass survives in the mean ordinary
floor loss, uniformly through a fixed positive multiple of diagonal multiplicity. -/
theorem successorSquare_mean_floor_loss : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ {M : ℕ}, 0 < M → K*(M:ℝ) ≤ n →
    (M:ℝ)*(n:ℝ)^2/768 ≤ ∑ m ∈ Icc M (3*M), ordinaryFloorLoss (m • successorSquareTriple n) := by
  obtain ⟨B,hB,hrow⟩ := row_error
  let W := successorSquareWindowScale
  have hWtop : Tendsto W atTop atTop := tendsto_atTop_mono (fun n => (successorSquareWindowScale_bounds n).1)
    ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hmass := hWtop.eventually (proportional_prime_mass (u := (1:ℝ)/3) (v := (1:ℝ)/2) (by norm_num) (by norm_num))
  refine ⟨8192*B,by linarith only [hB],?_⟩
  filter_upwards [hmass,eventually_ge_atTop 1] with n hw hn
  intro M hM hsmall
  let S := successorSquareWindowPrimes n
  let T := Icc M (3*M)
  let L := 3*windowEnd ((2*n+1)^2+1)
  let F := fun m k => Int.fract (actualRow n m k)
  have hW := successorSquareWindowScale_bounds n
  have hL₀ : 9 ≤ windowEnd ((2*n+1)^2+1) := by exact_mod_cast hW.2.1.trans hW.2.2
  have hL : 11 ≤ L := by dsimp only [L]; omega
  have hmass' : (n:ℝ)^2/12 ≤ ∑ k ∈ S, Real.log k := by
    have hh : W n/12 ≤ ∑ k ∈ S, Real.log k := by
      simpa only [S,successorSquareWindowPrimes,one_div_mul_eq_div,
        show ((1:ℝ)/2-1/3)/2=1/12 by norm_num,W] using hw
    exact (div_le_div_of_nonneg_right hW.1 (by norm_num)).trans hh
  have hmem {k : ℕ} (hk : k ∈ S) : k.Prime ∧ W n/3 < k ∧ (k:ℝ) ≤ W n/2 := by
    obtain ⟨hi,hp⟩ := mem_filter.mp hk
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
    exact ⟨hp,(Nat.floor_lt (by linarith only [hW.2.1] : 0 ≤ W n/3)).mp hl,
      (Nat.cast_le.mpr hu).trans (Nat.floor_le (by linarith only [hW.2.1] : 0 ≤ W n/2))⟩
  have hsub : S ⊆ ordinaryPrimeLags L := by
    intro k hk
    obtain ⟨hp,_,hu⟩ := hmem hk
    have hk' : k ≤ windowEnd ((2*n+1)^2+1) := by
      have he : (k:ℝ) ≤ windowEnd ((2*n+1)^2+1) := by linarith only [hu,hW.2.1,hW.2.2]
      exact_mod_cast he
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,by dsimp only [L]; omega⟩,hp⟩
  have havg {k : ℕ} (hk : k ∈ S) : (M:ℝ)/64 ≤ ∑ m ∈ T, F m k := by
    obtain ⟨hp,hl,hu⟩ := hmem hk
    let b := integratedContact (successorSquareTriple n) k
    have hroot := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos : (0:ℝ) < k)
    have hscale : (n:ℝ) ≤ 2*Real.sqrt k := by
      have hs : (n:ℝ)^2 ≤ (2*Real.sqrt k)^2 := by
        linarith only [hW.1,hl,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k),Nat.cast_nonneg (α := ℝ) k]
      simpa only [Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) n),
        Real.sqrt_sq (by positivity : 0 ≤ 2*Real.sqrt k)] using Real.sqrt_le_sqrt hs
    obtain ⟨hb,he⟩ := hrow n hp.pos
    apply negative_quadratic_floor_loss hM (b := b)
    · apply (le_of_mul_le_mul_right _ hroot)
      have hh := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) M)
      change |b| * Real.sqrt k * M ≤ _ at hh
      linarith only [hh,hscale,hsmall]
    · intro m hm
      obtain ⟨hm₁,hm₂⟩ := mem_Icc.mp hm
      have hm' := hM.trans_le hm₁
      have hr := hm'.trans_le (successorSquare_resolution_ge n m)
      have hneg : actualRow n m k < 0 := by
        change contactMultiplicity (packet (m • successorSquareTriple n)) L (resolution (m • successorSquareTriple n)) k < 0
        rw [packet_smul,contactMultiplicity_scale]
        exact mul_neg_of_pos_of_neg (sq_pos_of_pos (Nat.cast_pos.mpr hm'))
          (successorSquare_negative_window hn hr hL hl hu)
      refine ⟨hneg,le_of_mul_le_mul_right ?_ hroot⟩
      have ht : (m:ℝ) ≤ 3*M := by exact_mod_cast hm₂
      have he' : |actualRow n m k-b*(m:ℝ)^2| * Real.sqrt k ≤ B*m := he hm'
      linarith only [he',mul_le_mul_of_nonneg_left ht (zero_le_one.trans hB),hscale,hsmall]
  have hlog {k : ℕ} (hk : k ∈ S) : Real.log k = vonMangoldt k := by
    have hp := (hmem hk).1
    rw [← log_contactBase,contactBase,if_pos hp.isPrimePow,hp.minFac_eq]
  calc (M:ℝ)*(n:ℝ)^2/768 = ((M:ℝ)/64)*((n:ℝ)^2/12) := by ring
    _ ≤ ((M:ℝ)/64)*∑ k ∈ S, Real.log k := mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ ≤ ∑ k ∈ S, ∑ m ∈ T, F m k*vonMangoldt k := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      rw [hlog hk,← sum_mul]
      exact mul_le_mul_of_nonneg_right (havg hk) vonMangoldt_nonneg
    _ = ∑ m ∈ T, ∑ k ∈ S, F m k*vonMangoldt k := sum_comm
    _ ≤ _ := sum_le_sum fun m _ => sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => mul_nonneg (Int.fract_nonneg _) vonMangoldt_nonneg)

/-- At every such scale one multiplicity realizes a quadratic saving in the
logarithm of its actual signed ordinary-prime generator. -/
theorem successorSquare_exists_floor_loss : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ {M : ℕ}, 0 < M → K*(M:ℝ) ≤ n → ∃ m ∈ Icc M (3*M),
      (n:ℝ)^2/2304 ≤ ordinaryFloorLoss (m • successorSquareTriple n) := by
  obtain ⟨K,hK,h⟩ := successorSquare_mean_floor_loss
  refine ⟨K,hK,?_⟩
  filter_upwards [h] with n hn
  intro M hM hm
  apply exists_le_of_sum_le ⟨M,mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
  refine le_trans ?_ (hn hM hm)
  rw [sum_const,Nat.card_Icc,nsmul_eq_mul]
  have hcard : ((3*M+1-M : ℕ):ℝ) ≤ 3*M := by exact_mod_cast (show 3*M+1-M ≤ 3*M by omega)
  linarith only [mul_le_mul_of_nonneg_right hcard (sq_nonneg (n:ℝ))]

#print axioms successorSquare_mean_floor_loss
#print axioms successorSquare_exists_floor_loss

end GaloisForLFunctions.CountingHolography.Sections
