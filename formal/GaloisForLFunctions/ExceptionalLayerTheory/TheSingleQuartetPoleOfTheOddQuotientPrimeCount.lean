import GaloisForLFunctions.ExceptionalLayerTheory.TheQuarterExponentOfTheOddQuotientPrimeCount
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity

/-!
# The half-height prime-divisor pole on the single-quartet stratum

At half the right zero the unscaled zeta factor is nonzero, and three
times that point is outside the possible zero ratios. The normalized
finite odd-quotient mean therefore has sharp power exponent Re ρ / 2.
-/

noncomputable section
open Complex Filter Topology Set
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory
open ExclusionOfTheCriticalState

private theorem scaled_nonzero {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) (hoff : a*ρ.re ≠ 1/2) : riemannZeta ((a:ℂ)*ρ) ≠ 0 := by
  intro hz
  have hpos : 0 < ((a:ℂ)*ρ).re := by simpa using mul_pos ha hq.2.1.2.1
  have hlt : ((a:ℂ)*ρ).re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz
  have hmem : (a:ℂ)*ρ ∈ zeroQuartetSet ρ := by
    rw [← hq.2.2]
    exact ⟨⟨hz,hpos,hlt⟩,by simpa using hoff⟩
  have hag : |((a:ℂ)*ρ).im|=|ρ.im| := by
    simp only [zeroQuartetSet,Set.mem_insert_iff,Set.mem_singleton_iff] at hmem
    rcases hmem with e | e | e | e <;> rw [e] <;> simp
  have him := abs_pos.mpr hq.im_ne_zero
  rw [Complex.im_ofReal_mul,abs_mul,abs_of_pos ha] at hag
  exact ha1 ((mul_right_cancel₀ him.ne') (hag.trans (one_mul _).symm))

private theorem half_ne_zero {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) : riemannZeta (ρ/2) ≠ 0 := by
  have h := scaled_nonzero hq (a := 1/2) (by norm_num) (by norm_num) (by linarith only [hq.re_lt_one])
  rwa [show (((1/2:ℝ):ℂ)*ρ)=ρ/2 by push_cast; ring] at h

/-- At half the right zero the residue contains precisely its multiplicity.
The cube contributes no zero there and the unscaled zeta factor is nonzero. -/
theorem firstPrimeDivisorMoment_singleQuartet_residue {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    Tendsto (fun w => (w-ρ/2)*firstPrimeDivisorMoment w) (𝓝[≠] (ρ/2))
      (𝓝 (riemannZeta (ρ/2)*((analyticOrderNatAt riemannZeta ρ:ℂ)/2))) := by
  have h₁ : 1/4 < (ρ/2).re := by rw [Complex.div_ofNat_re]; linarith only [hq.1]
  have hi : (ρ/2).im ≠ 0 := by simpa [Complex.div_ofNat_im] using hq.im_ne_zero
  have h := firstPrimeDivisorMoment_exact_residue h₁ hi
  have h₃ := scaled_nonzero hq (a := 3/2) (by norm_num) (by norm_num) (by linarith only [hq.1])
  have he : (((3/2:ℝ):ℂ)*ρ) = 3*(ρ/2) := by push_cast; ring
  rw [he] at h₃
  have hn : analyticOrderNatAt riemannZeta (3*(ρ/2)) = 0 := by
    by_contra hne
    exact h₃ (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)
  simpa only [show 2*(ρ/2)=ρ by ring,hn,Nat.cast_zero,zero_div,add_zero] using h

private theorem abscissa_le_quartet {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) : zeroReSup ≤ ρ.re := by
  apply zeroReSup_le_of_forall_re_le
  intro q
  by_cases hh : (q.1:ℂ).re = 1/2
  · rw [hh]; exact hq.1.le
  have hmem : (q.1:ℂ) ∈ zeroQuartetSet ρ := by
    rw [← hq.2.2]
    exact ⟨⟨riemannZeta_eq_zero_of_xiZeroCopy q,xiZeroCopy_re_pos q,xiZeroCopy_re_lt_one q⟩,hh⟩
  have he : (q.1:ℂ).re=ρ.re ∨ (q.1:ℂ).re=1-ρ.re := by
    simp only [zeroQuartetSet,Set.mem_insert_iff,Set.mem_singleton_iff] at hmem
    rcases hmem with e | e | e | e <;> simp [e]
  rcases he with he | he <;> linarith only [he,hq.1]

/-- Every power bound for the normalized finite count lies at or above
half the right-zero abscissa, and each strictly larger exponent works. -/
theorem oddQuotientPowerTotal_singleQuartet_exponent {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    (∀ b : ℝ, ρ.re/2 < b → ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(b+1)) ∧
    (∀ b : ℝ, (∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(b+1)) → ρ.re/2 ≤ b) := by
  have hpos : 1/4 < ρ.re/2 := by linarith only [hq.1]
  have hlt : ρ.re/2 < 1/2 := by linarith only [hq.re_lt_one]
  constructor
  · intro b hb
    obtain ⟨a,ha,ham⟩ := exists_between (lt_min hb hlt)
    obtain ⟨C,hC,h⟩ := properPowerDiscrepancy_bound_above_abscissa
      (show zeroReSup/2 < a by linarith only [abscissa_le_quartet hq,ha])
    have ha0 : 0 < a := by linarith only [hpos,ha]
    have hK : 0 ≤ (C+2)/a := by positivity
    refine ⟨_,hK,fun N hn => ?_⟩
    have h1 : (1:ℝ) ≤ N := by exact_mod_cast hn
    apply (oddQuotientPowerTotal_bound ha0 (by linarith only [(lt_min_iff.mp ham).2]) hC h hn).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1
      (by linarith only [(lt_min_iff.mp ham).1])) hK
  · rintro b ⟨K,hK,h⟩
    by_contra! hsmall
    obtain ⟨a,ha,haρ⟩ := exists_between (max_lt hsmall hpos)
    have hb := (max_lt_iff.mp ha).1
    have hlow := (max_lt_iff.mp ha).2
    have hN (N : ℕ) (hn : 1 ≤ N) : |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(a+1) :=
      (h N hn).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hn : (1:ℝ) ≤ N) (by linarith only [hb])) hK)
    have hr : (ρ/2).re = ρ.re/2 := by simp [Complex.div_ofNat_re]
    have hi : (ρ/2).im ≠ 0 := by simpa [Complex.div_ofNat_im] using hq.im_ne_zero
    have hz := firstPrimeDivisorMoment_zero_residue_of_oddQuotientPowerTotal_bound hlow
      (haρ.trans hlt) hK hN (by rw [hr]; exact haρ) (by rw [hr]; exact hlt) hi
    have hm := one_le_analyticOrderAt_riemannZeta_toNat
      (show ρ ≠ 1 from fun e => hq.im_ne_zero (by rw [e,one_im])) hq.2.1.1
    have hnat : 0 < analyticOrderNatAt riemannZeta ρ := hm
    have hc : (analyticOrderNatAt riemannZeta ρ:ℂ) ≠ 0 := by exact_mod_cast hnat.ne'
    exact (mul_ne_zero (half_ne_zero hq) (div_ne_zero hc (by norm_num)))
      (tendsto_nhds_unique (firstPrimeDivisorMoment_singleQuartet_residue hq) hz)

end GaloisForLFunctions.ExceptionalLayerTheory
