import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RowLabelWeights
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.IrreducibleLocalCountRanges
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalCharacterCollisionWeights
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalRootCollisionWeights
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalFactorDegreeWeights

/-! The large-rank family tail supplies the five local weights
at both auxiliary primes. The join and its row counts then give
the irreducible-row link. -/

noncomputable section

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace WindowedLandauTheory.ConcN

local instance factGForBounds {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime :=
  ⟨D.host.g_prime k⟩

private theorem bounds_at_host (D : D7) (k : Fin 2) (hr : 20000 ≤ D.R.r)
    (hg : 2 ^ 12 ≤ D.host.g k) : LocalRowWeightBounds (D.host.g k) D.R.r D.host.q D.host.d := by
  have hr1 : 1 ≤ D.R.r := (by norm_num : 1 ≤ 20000).trans hr
  obtain ⟨hq, hd, hqd, hq2, hd2, hmax, h16, hqg, hdg⟩ := host_facts (tieAdmG_holds D) k
  exact ⟨square_mass_lower_bound _ _ hr1, local_root_collision_weight_le _ _ hg,
    fun c₀ => local_character_collision_weight_le _ _ _ _ c₀ hr1 hq hd hqd hq2 hd2 hmax h16 hqg hdg,
    local_divisor_degree_weight_le _ _, local_no_long_prime_weight_le _ _ hr⟩

private theorem rank_ge_of_sizes {D : D7} {x z Cs : ℝ}
    (hs : SizesRec D x z Cs) (hx : 142 ≤ x) : 20000 ≤ D.R.r := by
  have hf : x ^ 2 ≤ (D.R.f : ℝ) := (hs 0).2.1
  have hfr : D.R.f ≤ D.R.r := by
    have hfk : D.R.f ≤ D.R.k := by simpa only [Ranks.f, Ranks.n] using D.R.f_le_k
    have hkr : D.R.k ≤ D.R.r := by
      have hm := D.R.two_le_m
      unfold Ranks.r
      omega
    exact hfk.trans hkr
  have hx2 : (20000 : ℝ) ≤ x ^ 2 :=
    (show (20000 : ℝ) ≤ (142 : ℝ) ^ 2 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hx 2)
  exact_mod_cast (hx2.trans hf).trans (Nat.cast_le.mpr hfr : (D.R.f : ℝ) ≤ D.R.r)

theorem linkIRR_of_join_ex (eps Cs c : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) (hc : 0 < c)
    (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧ AllJoinA A ∧ admLq (Fm.D x i) ∧
      CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
      SizesRec (Fm.D x i) x Fm.ez Cs) : LinkIRR Fm := by
  obtain ⟨x0, hx0⟩ := h
  have hez : 0 < Fm.ez := div_pos he (zero_lt_one.trans_le Fm.one_le_J)
  let y := max (142 : ℝ) ((3 / 2 : ℝ) ^ (1 / Fm.ez))
  refine linkIRR_of_allRows eps Cs c he he1 hc Fm ⟨max x0 y, fun x hx i => ?_⟩
  obtain ⟨A, hT, hJ, hL, hC, hS⟩ := hx0 x ((le_max_left _ _).trans hx) i
  have hy : y ≤ x := (le_max_right _ _).trans hx
  have hx142 : 142 ≤ x := (le_max_left _ _).trans hy
  have hxpow : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := (le_max_right _ _).trans hy
  have hxz : 3 / 2 ≤ x ^ Fm.ez := by
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow (by positivity) hxpow hez.le
  have hr := rank_ge_of_sizes hS hx142
  have hG := (rangeW_of_sizes hS hxz).2
  exact ⟨A, hT, hC, weight_of_join A hL hJ (fun k => bounds_at_host (Fm.D x i) k hr (hG k)), hS⟩

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.linkIRR_of_join_ex
