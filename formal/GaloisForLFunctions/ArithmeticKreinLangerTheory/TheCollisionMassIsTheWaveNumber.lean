import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheIndexIsTheNumberOfExceptionalWaves
import GaloisForLFunctions.HeckeKreinToeplitz.HeatCollisionsCountTheIndex
import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum
import GaloisForLFunctions.RHTower.XiZeroCountingFunction
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# The collision mass is the wave number

Along the de Bruijn–Newman flow, nonreal zeros collide on the real axis; on the finite stratum the
collision mass after small times is `2(κ(K_ζ) + E)`, `E` the multiplicity excess (HKT,
`eventually_collisionMassAfter_eq_index`). This module reads `κ(K_ζ)` on the prime side.

**The Weil kernel on the finite stratum, presented** (`zetaKernel_eq_onLine_add_pairs_fin`). The
kernel is the positive-definite orbit kernel of the on-line zeros plus one hyperbolic pair per right
zero, with nonzero weight because the cubic spline sees every zero (`Wsummand_ne_zero_of_rightZero`).

**Collisions count exceptional waves** (`waveNumber_collision_law`). There is a tower `⟨u⟩` along
which the values `K_ζ(u^n)` (prime sums against translated tests, by the explicit formula) form a
count with the following property: it is bounded after subtracting `κ` waves, it is bounded after
subtracting `m` waves only if `m ≥ κ`, and the collision mass after small times is
`2(κ + E)`. The near-axis collisions are therefore governed by the **wave number** of the prime-side
count, the least number of exceptional exponentials it needs, plus the multiplicity excess.

**A minimal count reads the multiplicities** (`minimal_count_reads_multiplicities`). A count bounded
after exactly `κ` waves uses one wave per right zero, with amplitude `m_ρ |ĝ(γ_ρ)| |ĝ(γ̄_ρ)|`: the
zero multiplicities, and with them the excess `E`, are read off the amplitudes of a minimal count.

**The collision law read from one count** (`xiMult_eq_mult`, `collision_mass_from_minimal_count`).
The order of `ξ` at a zero is its multiplicity as a zero of `ζ`, so the heat-collision mass after
small times, `2(κ + Σ(m_ρ − 1))`, is determined by a minimal count: its number of waves and their
amplitudes.
-/

open Complex Finset Filter Topology Zeta23
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros cx realTests)
open GaloisForLFunctions.ArithmeticOrientationGeometry (xiMult seenRightZeros seenRightZeros_cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open RHTower RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- **The spline sees every right zero**: its weight in the Weil kernel is nonzero. -/
theorem Wsummand_ne_zero_of_rightZero {ρ : ℂ} (hρ : ρ ∈ rightZeros zetaZeroConfig) :
    zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ ≠ 0 := by
  have hs : ρ ∈ seenRightZeros zetaZeroConfig cubicSpline := by
    rw [seenRightZeros_cubicSpline]; exact hρ
  obtain ⟨hc, -, h1, h2⟩ := hs
  simp only [ZeroConfig.Wsummand]
  refine mul_ne_zero (mul_ne_zero ?_ h1) ((_root_.map_ne_zero _).mpr h2)
  have h1 := zetaZeroConfig.one_le_mult ρ hc
  exact_mod_cast (by omega : zetaZeroConfig.mult ρ ≠ 0)

/-- **The Weil kernel on the finite stratum, presented over `Fin κ`.** -/
theorem zetaKernel_eq_onLine_add_pairs_fin (hfin : (rightZeros zetaZeroConfig).Finite)
    (g : HeckeLattice) :
    zetaKernel g = orbitKernel (onLineConfig zetaZeroConfig) cubicSpline g +
      ∑ j : Fin hfin.toFinset.card, pairKernel (zeroChar (conj (hfin.toFinset.equivFin.symm j : ℂ)))
        (conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline)
          (hfin.toFinset.equivFin.symm j : ℂ))) g := by
  rw [zetaKernel, orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests hfin]
  congr 1
  rw [← Finset.sum_coe_sort hfin.toFinset, ← hfin.toFinset.equivFin.symm.sum_comp]

/-- **Collisions count exceptional waves.** On the finite stratum there is a tower `⟨u⟩` such that
the Weil-kernel count along it is bounded after subtracting `κ = #(right zeros)` waves and after
subtracting `m` waves only if `κ ≤ m`, while the collision mass after small times is
`2(κ + E)`. -/
theorem waveNumber_collision_law (h : negIndex zetaKernel < ⊤) :
    ∃ (hfin : (rightZeros zetaZeroConfig).Finite) (u : HeckeLattice),
      negIndex zetaKernel = hfin.toFinset.card ∧
      (∀ (m : ℕ) (v a : Fin m → ℂ), (∃ M, ∀ n : ℕ, ‖zetaKernel (u ^ n) -
        ∑ i, a i * v i ^ n‖ ≤ M) → hfin.toFinset.card ≤ m) ∧
      (∃ v a : Fin hfin.toFinset.card → ℂ, ∃ M, ∀ n : ℕ,
        ‖zetaKernel (u ^ n) - ∑ i, a i * v i ^ n‖ ≤ M) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), collisionMassAfter t =
        2 * (hfin.toFinset.card + ∑ ρ ∈ hfin.toFinset, (xiMult ρ - 1)) := by
  obtain ⟨hfin, hκ, hev⟩ := eventually_collisionMassAfter_eq_index h
  set R := hfin.toFinset with hR
  set e := R.equivFin
  have hρR : ∀ j, ((e.symm j : ℂ)) ∈ rightZeros zetaZeroConfig := fun j =>
    hfin.mem_toFinset.mp (e.symm j).2
  have hp := isPosDefKernel_orbitKernel_onLine temperedConfig_zetaZeroConfig cubicSpline_mem_realTests
  have hω : ∀ j, conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) (e.symm j : ℂ)) ≠ 0 :=
    fun j => (_root_.map_ne_zero _).mpr (Wsummand_ne_zero_of_rightZero (hρR j))
  obtain ⟨u, hne, hsep⟩ := exists_separating_of_small heckeLogScale heckeLogScale_small
    (fun j => conj (e.symm j : ℂ) - 1 / 2)
    (fun i j hij => e.symm.injective (Subtype.ext ((RingHom.injective _) (sub_left_injective hij))))
    (fun j => by
      have := (hρR j).2
      simp only [sub_re, conj_re, one_div, inv_re, normSq_ofNat]
      norm_num
      linarith)
  obtain ⟨-, hceil, hatt⟩ := negIndex_eq_card_waves hp _ _ hω u hne hsep
  refine ⟨hfin, u, hκ, fun m v a hb => hceil m v a ?_, ?_, hev⟩
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun n => by rw [← zetaKernel_eq_onLine_add_pairs_fin hfin]; exact hM n⟩
  · obtain ⟨v, a, M, hM⟩ := hatt
    exact ⟨v, a, M, fun n => by rw [zetaKernel_eq_onLine_add_pairs_fin hfin]; exact hM n⟩

/-- **A minimal count reads the multiplicities.** On the finite stratum there is a tower `⟨u⟩` such
that every count along it bounded after exactly `κ` waves uses one wave per right zero, with
amplitude `m_ρ · |ĝ(γ_ρ)| · |ĝ(γ̄_ρ)|`: the multiplicity times the spline factor. -/
theorem minimal_count_reads_multiplicities (h : negIndex zetaKernel < ⊤) :
    ∃ (hfin : (rightZeros zetaZeroConfig).Finite) (u : HeckeLattice),
      ∀ v a : Fin hfin.toFinset.card → ℂ, (∃ M, ∀ n : ℕ,
        ‖zetaKernel (u ^ n) - ∑ i, a i * v i ^ n‖ ≤ M) →
      ∃ σ : Fin hfin.toFinset.card ≃ Fin hfin.toFinset.card, ∀ j,
        ‖a (σ j)‖ = (zetaZeroConfig.mult (hfin.toFinset.equivFin.symm j : ℂ) : ℝ) *
          ‖paperFT (cx cubicSpline) (gammaOf (hfin.toFinset.equivFin.symm j : ℂ))‖ *
          ‖paperFT (cx cubicSpline) (conj (gammaOf (hfin.toFinset.equivFin.symm j : ℂ)))‖ := by
  obtain ⟨hfin, -, -⟩ := eventually_collisionMassAfter_eq_index h
  set R := hfin.toFinset with hR
  set e := R.equivFin
  have hρR : ∀ j, ((e.symm j : ℂ)) ∈ rightZeros zetaZeroConfig := fun j =>
    hfin.mem_toFinset.mp (e.symm j).2
  have hp := isPosDefKernel_orbitKernel_onLine temperedConfig_zetaZeroConfig cubicSpline_mem_realTests
  have hω : ∀ j, conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) (e.symm j : ℂ)) ≠ 0 :=
    fun j => (_root_.map_ne_zero _).mpr (Wsummand_ne_zero_of_rightZero (hρR j))
  obtain ⟨u, hne, hsep⟩ := exists_separating_of_small heckeLogScale heckeLogScale_small
    (fun j => conj (e.symm j : ℂ) - 1 / 2)
    (fun i j hij => e.symm.injective (Subtype.ext ((RingHom.injective _) (sub_left_injective hij))))
    (fun j => by
      have := (hρR j).2
      simp only [sub_re, conj_re, one_div, inv_re, normSq_ofNat]
      norm_num
      linarith)
  refine ⟨hfin, u, fun v a hb => ?_⟩
  obtain ⟨σ, hσ⟩ := minimal_waves_eq_outerNodes hp _ _ hω u hne hsep v a (by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun n => by rw [← zetaKernel_eq_onLine_add_pairs_fin hfin]; exact hM n⟩)
  refine ⟨σ, fun j => ?_⟩
  rw [(hσ j).2]
  have hnorm : ‖nodeCoeff (fun j => conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline)
      (e.symm j : ℂ))) (outerNode (fun j => zeroChar (conj (e.symm j : ℂ))) u j)‖ =
      ‖zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) (e.symm j : ℂ)‖ := by
    unfold outerNode; split_ifs
    · simp [nodeCoeff]
    · simp [nodeCoeff]
  rw [hnorm]
  simp only [ZeroConfig.Wsummand, norm_mul, Complex.norm_natCast, Complex.norm_conj]
  rfl

/-! ### The multiplicity bridge and the collision law read from one count -/

/-- **The order of `ξ` is the multiplicity of the zero of `ζ`** in the critical strip. -/
theorem xiMult_eq_mult {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    xiMult ρ = zetaZeroConfig.mult ρ := by
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := by
    simp only [zetaZeroConfig_carrier, Set.mem_setOf_eq] at hρ
    exact hρ.2
  rw [xiMult, RHTower.xi_divisor_apply_of_mem (Set.mem_univ ρ), Int.toNat_natCast,
    RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip, zetaZeroConfig_mult]
  rfl

/-- **The collision law read from one count.** On the finite stratum there is a tower `⟨u⟩` and a
labelling `ρ_1, …, ρ_κ` of the right zeros such that every count along `⟨u⟩` bounded after exactly
`κ` waves has amplitudes `m_j · |ĝ(γ_j)| · |ĝ(γ̄_j)|`, and the collision mass after small times is
`2(κ + Σ_j (m_j − 1))`: index and multiplicity excess of the heat collisions are both read off the
minimal count. -/
theorem collision_mass_from_minimal_count (h : negIndex zetaKernel < ⊤) :
    ∃ (κ : ℕ) (ρ : Fin κ → ℂ) (u : HeckeLattice),
      negIndex zetaKernel = κ ∧
      (∀ v a : Fin κ → ℂ, (∃ M, ∀ n : ℕ, ‖zetaKernel (u ^ n) - ∑ i, a i * v i ^ n‖ ≤ M) →
        ∃ σ : Fin κ ≃ Fin κ, ∀ j, ‖a (σ j)‖ = (zetaZeroConfig.mult (ρ j) : ℝ) *
          ‖paperFT (cx cubicSpline) (gammaOf (ρ j))‖ *
          ‖paperFT (cx cubicSpline) (conj (gammaOf (ρ j)))‖) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), collisionMassAfter t =
        2 * (κ + ∑ j, (zetaZeroConfig.mult (ρ j) - 1)) := by
  obtain ⟨hfin, hκ, hev⟩ := eventually_collisionMassAfter_eq_index h
  obtain ⟨hfin', u, hmin⟩ := minimal_count_reads_multiplicities h
  have hR : hfin'.toFinset = hfin.toFinset := rfl
  refine ⟨hfin.toFinset.card, fun j => (hfin.toFinset.equivFin.symm j : ℂ), u, hκ, hmin, ?_⟩
  filter_upwards [hev] with t ht
  rw [ht]
  congr 2
  rw [← Finset.sum_coe_sort hfin.toFinset, ← hfin.toFinset.equivFin.symm.sum_comp]
  refine sum_congr rfl fun j _ => ?_
  rw [xiMult_eq_mult (hfin.mem_toFinset.mp (hfin.toFinset.equivFin.symm j).2).1]

end GaloisForLFunctions.ArithmeticKreinLangerTheory

open GaloisForLFunctions.ArithmeticKreinLangerTheory in
#print axioms collision_mass_from_minimal_count
