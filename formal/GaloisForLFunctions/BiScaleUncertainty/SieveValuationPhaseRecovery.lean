import GaloisForLFunctions.BiScaleUncertainty.MixedValuationQuintic
import GaloisForLFunctions.BiScaleUncertainty.SixthValuationPhaseRecovery
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Global valuation phase recovery from fifth and sixth moments

The existing quintic receiver orients every active valuation class below the
highest one. Sixth moments align the highest class up to one common sign.
A fifth-order diagonal orients odd modes, including zero-mean and empty-support
cases. No affine observations or nonvanishing-coordinate premises are needed.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ValuationPhase
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩


/-- Nonzero multiples coordinates inside the actual divisor cutoff. -/
def activeModes (N : ℕ) (c : ℕ → ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun q => selbergMultiplesCoord N c q ≠ 0)

/-- Greatest two-adic exponent of an active coordinate, zero for empty support. -/
def activeDepth (N : ℕ) (c : ℕ → ℝ) : ℕ :=
  (activeModes N c).sup (fun q => q.factorization 2)

/-- The existing canonical factorization in the odd-parameter form of the quintic readout. -/
theorem order_odd_decomposition {q : ℕ} (hq : 0 < q) :
    ∃ p : ℕ, q = 2 ^ (q.factorization 2) * (2*p+1) := by
  have hnot := Nat.not_dvd_ordCompl Nat.prime_two hq.ne'
  have ho : Odd (q / 2 ^ (q.factorization 2)) :=
    Nat.not_even_iff_odd.mp (fun he => hnot he.two_dvd)
  obtain ⟨p, hp⟩ := ho
  refine ⟨p, ?_⟩
  calc
    q = 2 ^ (q.factorization 2) * (q / 2 ^ (q.factorization 2)) :=
      (Nat.ordProj_mul_ordCompl_eq_self q 2).symm
    _ = _ := by congr 1

/-- Every active order lies below the greatest active valuation. -/
theorem depth_le_activeDepth (N q : ℕ) (c : ℕ → ℝ)
    (hq : q ∈ Finset.Icc 1 N) (hc : selbergMultiplesCoord N c q ≠ 0) :
    q.factorization 2 ≤ activeDepth N c := by
  unfold activeDepth
  exact Finset.le_sup (f := fun q : ℕ => q.factorization 2)
    (show q ∈ activeModes N c from Finset.mem_filter.mpr ⟨hq, hc⟩)

/-- Positive greatest depth is attained by an actual nonzero coordinate. -/
theorem exists_at_activeDepth (N : ℕ) (c : ℕ → ℝ) (hV : 0 < activeDepth N c) :
    ∃ q ∈ Finset.Icc 1 N, selbergMultiplesCoord N c q ≠ 0 ∧
      q.factorization 2 = activeDepth N c := by
  have hs : (activeModes N c).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have hv : activeDepth N c = 0 := by simp [activeDepth, hz]
    omega
  obtain ⟨q, hq, he⟩ := Finset.exists_mem_eq_sup (activeModes N c) hs
    (fun q => q.factorization 2)
  obtain ⟨hqI, hqne⟩ := Finset.mem_filter.mp hq
  exact ⟨q, hqI, hqne, he.symm⟩

private theorem squares_of_sixth (N : ℕ) (c e : ℕ → ℝ)
    (h6 : ∀ v : Fin 6 → ℕ, translatedMoment N c v = translatedMoment N e v)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
    selbergMultiplesCoord N c q ^ 2 = selbergMultiplesCoord N e q ^ 2 := by
  obtain ⟨p, hp⟩ := order_odd_decomposition (Finset.mem_Icc.mp hq).1
  have ho : Odd (2*p+1) := ⟨p, by omega⟩
  rcases sixth_moments_recover_valuation_block N (q.factorization 2) c e h6 with hs | hs
  · have he := hs (2*p+1) ho (hp ▸ hq)
    simpa only [← hp] using congrArg (fun x : ℝ => x^2) he
  · have he := hs (2*p+1) ho (hp ▸ hq)
    rw [← hp] at he
    rw [he]
    ring

private theorem odd_coordinates_of_fifth (N : ℕ) (c e : ℕ → ℝ)
    (h5 : ∀ v : Fin 5 → ℕ, translatedMoment N c v = translatedMoment N e v)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 N) (ho : Odd q) :
    selbergMultiplesCoord N c q = selbergMultiplesCoord N e q := by
  let r : ZMod N.factorial := (N.factorial/q : ℕ)
  have hr : addOrderOf r = q := frequency_order hq
  have hg : Nat.gcd q 2 = 1 := ho.coprime_two_right
  have hrr : addOrderOf (r+r) = q := by
    simpa only [two_nsmul, hr, hg, Nat.div_one] using (addOrderOf_nsmul (n := 2) r)
  let v : Fin 5 → ZMod N.factorial := ![r,r,-(r+r),r,-r]
  have hsum : (∑ i, v i) = 0 := by
    simp [v, Fin.sum_univ_succ]
  have hprod (y : ℕ → ℂ) : (∏ i, y (addOrderOf (v i))) = y q ^ 5 := by
    simp only [Fin.prod_univ_succ]
    change y (addOrderOf r) * (y (addOrderOf r) * (y (addOrderOf (-(r+r))) *
      (y (addOrderOf r) * (y (addOrderOf (-r)) * 1)))) = y q ^ 5
    rw [addOrderOf_neg, addOrderOf_neg, hr, hrr]
    ring
  have hobs :
      (fun h : Fin 5 → ZMod N.factorial => (translatedMoment N c (fun i => (h i).val) : ℂ)) =
      (fun h : Fin 5 → ZMod N.factorial => (translatedMoment N e (fun i => (h i).val) : ℂ)) := by
    funext h
    rw [h5]
  have he := congrArg (fun f : (Fin 5 → ZMod N.factorial) → ℂ => momentDFT f v) hobs
  simp only [translatedMoment_complex_eq, ZMod.natCast_zmod_val] at he
  change momentDFT (translationMoment (residueSignal N (fun d => (c d : ℂ)))) v =
    momentDFT (translationMoment (residueSignal N (fun d => (e d : ℂ)))) v at he
  simp only [momentDFT_sieve, hsum, if_true] at he
  rw [hprod (coordinate N (fun d => (c d : ℂ))),
    hprod (coordinate N (fun d => (e d : ℂ)))] at he
  simp only [coordinate_ofReal] at he
  have hP : (N.factorial : ℂ)^5 ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero N)
  have hpower := mul_left_cancel₀ hP he
  have hreal : selbergMultiplesCoord N c q ^ 5 = selbergMultiplesCoord N e q ^ 5 := by
    exact_mod_cast hpower
  exact (show Odd (5 : ℕ) from ⟨2, rfl⟩).pow_injective hreal

/-- The existing quintic receiver orients any lower order at an arbitrary common cutoff. -/
theorem lower_coordinate_of_fifth (N : ℕ) (c e : ℕ → ℝ)
    (h5 : ∀ v : Fin 5 → ℕ, translatedMoment N c v = translatedMoment N e v)
    {d u : ℕ} (hd : d ∈ Finset.Icc 1 N) (hu : u ∈ Finset.Icc 1 N)
    (hdu : d.factorization 2 < u.factorization 2)
    (hsq : selbergMultiplesCoord N c u ^ 2 = selbergMultiplesCoord N e u ^ 2) :
    selbergMultiplesCoord N c u = 0 ∨ selbergMultiplesCoord N c d = selbergMultiplesCoord N e d := by
  obtain ⟨p, hp⟩ := order_odd_decomposition (Finset.mem_Icc.mp hd).1
  obtain ⟨q, hq⟩ := order_odd_decomposition (Finset.mem_Icc.mp hu).1
  let k := d.factorization 2
  let s := u.factorization 2 - k - 1
  have hk : k + (s+1) = u.factorization 2 := by dsimp [k,s]; omega
  have hlow : MixedValuation.lowerOrder k p = d := hp.symm
  have hupp : MixedValuation.upperOrder k s q = u := by
    unfold MixedValuation.upperOrder
    rw [hk]
    exact hq.symm
  let n := N - max d u
  have hcut : MixedValuation.cutoff n k s p q = N := by
    unfold MixedValuation.cutoff
    rw [hlow, hupp]
    dsimp [n]
    have := (Finset.mem_Icc.mp hd).2
    have := (Finset.mem_Icc.mp hu).2
    omega
  have hobs : ∀ v : Fin 5 → ℕ,
      translatedMoment (MixedValuation.cutoff n k s p q) c v =
        translatedMoment (MixedValuation.cutoff n k s p q) e v := by
    rw [hcut]
    exact h5
  have hread : MixedValuation.fifthReadout n k s p q c =
      MixedValuation.fifthReadout n k s p q e := by
    unfold MixedValuation.fifthReadout
    simp_rw [hobs]
  have hs : selbergMultiplesCoord (MixedValuation.cutoff n k s p q) c
        (MixedValuation.upperOrder k s q)^2 =
      selbergMultiplesCoord (MixedValuation.cutoff n k s p q) e
        (MixedValuation.upperOrder k s q)^2 := by
    rw [hcut, hupp]
    exact hsq
  have he := (MixedValuation.fifthReadout_and_upper_sq_iff n k s p q c e).mp ⟨hread, hs⟩
  rw [hcut, hlow, hupp] at he
  exact he.2

/-- Fifth and sixth translated data leave at most the common sign of the greatest active valuation. -/
theorem coordinates_eq_or_highest_flip (N : ℕ) (c e : ℕ → ℝ)
    (h5 : ∀ v : Fin 5 → ℕ, translatedMoment N c v = translatedMoment N e v)
    (h6 : ∀ v : Fin 6 → ℕ, translatedMoment N c v = translatedMoment N e v) :
    (∀ q ∈ Finset.Icc 1 N, selbergMultiplesCoord N e q = selbergMultiplesCoord N c q) ∨
      (0 < activeDepth N c ∧ ∀ q ∈ Finset.Icc 1 N,
        selbergMultiplesCoord N e q = if q.factorization 2 = activeDepth N c
          then -selbergMultiplesCoord N c q else selbergMultiplesCoord N c q) := by
  have hz (q : ℕ) (hq : q ∈ Finset.Icc 1 N) (hc : selbergMultiplesCoord N c q = 0) :
      selbergMultiplesCoord N e q = 0 := by
    apply sq_eq_zero_iff.mp
    rw [← squares_of_sixth N c e h6 q hq, hc]
    simp
  by_cases hV : activeDepth N c = 0
  · left
    intro q hq
    by_cases hc : selbergMultiplesCoord N c q = 0
    · rw [hz q hq hc, hc]
    · have hv : q.factorization 2 = 0 := by
        have hb := depth_le_activeDepth N q c hq hc
        omega
      obtain ⟨p, hp⟩ := order_odd_decomposition (Finset.mem_Icc.mp hq).1
      have ho : Odd q := by
        rw [hv, pow_zero, one_mul] at hp
        exact ⟨p, by omega⟩
      exact (odd_coordinates_of_fifth N c e h5 q hq ho).symm
  · have hVpos : 0 < activeDepth N c := Nat.pos_of_ne_zero hV
    obtain ⟨u, hu, hune, huV⟩ := exists_at_activeDepth N c hVpos
    have hlower (q : ℕ) (hq : q ∈ Finset.Icc 1 N)
        (hql : q.factorization 2 < activeDepth N c) :
        selbergMultiplesCoord N e q = selbergMultiplesCoord N c q := by
      have he := lower_coordinate_of_fifth N c e h5 hq hu (by omega)
        (squares_of_sixth N c e h6 u hu)
      exact (he.resolve_left hune).symm
    rcases sixth_moments_recover_valuation_block N (activeDepth N c) c e h6 with htop | htop
    · left
      intro q hq
      by_cases hc : selbergMultiplesCoord N c q = 0
      · rw [hz q hq hc, hc]
      · have hb := depth_le_activeDepth N q c hq hc
        by_cases hqt : q.factorization 2 = activeDepth N c
        · obtain ⟨p, hp⟩ := order_odd_decomposition (Finset.mem_Icc.mp hq).1
          rw [hqt] at hp
          have he := htop (2*p+1) (show Odd (2*p+1) from ⟨p, by omega⟩) (hp ▸ hq)
          simpa only [← hp] using he.symm
        · exact hlower q hq (by omega)
    · right
      refine ⟨hVpos, ?_⟩
      intro q hq
      by_cases hc : selbergMultiplesCoord N c q = 0
      · rw [hz q hq hc, hc]
        split_ifs <;> simp
      · have hb := depth_le_activeDepth N q c hq hc
        by_cases hqt : q.factorization 2 = activeDepth N c
        · rw [if_pos hqt]
          obtain ⟨p, hp⟩ := order_odd_decomposition (Finset.mem_Icc.mp hq).1
          rw [hqt] at hp
          have he := htop (2*p+1) (show Odd (2*p+1) from ⟨p, by omega⟩) (hp ▸ hq)
          rw [← hp] at he
          linarith
        · rw [if_neg hqt]
          exact hlower q hq (by omega)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ValuationPhase
